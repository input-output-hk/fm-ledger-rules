{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- The STS instance for UTXO is technically an orphan.
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Alonzo.Rules.Utxo where

import Cardano.Binary (FromCBOR (..), ToCBOR (..), serialize)
import Cardano.Ledger.Alonzo.PParams ()
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices, scriptfee)
import Cardano.Ledger.Alonzo.Tx
  ( Tx (..),
    isNonNativeScriptAddress,
    txbody,
    txsize,
  )
import Cardano.Ledger.Alonzo.TxBody
  ( TxOut (..),
    txExunits,
    txUpdates,
    txfee,
    txinputs_fee,
  )
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo (TxBody, TxOut)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import qualified Cardano.Ledger.Mary.Value as Alonzo (Value)
import Cardano.Ledger.Shelley.Constraints
  ( TransValue,
    UsesPParams,
  )
{-
  ( PParams,
    PParams'(_maxTxExUnits),
  )
-}

import Cardano.Ledger.ShelleyMA.Rules.Utxo (consumed, scaledMinDeposit)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..), inInterval)
import Cardano.Ledger.Val ((<+>), (<×>))
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.Slot (SlotNo)
import Control.Iterate.SetAlgebra (dom, eval, (⊆), (◁), (➖))
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended
import qualified Data.ByteString.Lazy as BSL (length)
import Data.Coders
  ( Decode (..),
    Encode (..),
    Wrapped (Open),
    decode,
    decodeList,
    decodeSet,
    encode,
    encodeFoldable,
    (!>),
    (<!),
  )
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.Address
  ( Addr (AddrBootstrap),
    RewardAcnt,
    bootstrapAddressAttrsSize,
    getNetwork,
    getRwdNetwork,
  )
import Shelley.Spec.Ledger.BaseTypes
  ( Network,
    ShelleyBase,
    StrictMaybe (..),
    networkId,
  )
import Shelley.Spec.Ledger.Coin
import Shelley.Spec.Ledger.LedgerState (PPUPState)
import qualified Shelley.Spec.Ledger.LedgerState as Shelley
import Shelley.Spec.Ledger.PParams (Update (..))
import Shelley.Spec.Ledger.STS.Ppup (PPUP, PPUPEnv (..), PpupPredicateFailure)
import qualified Shelley.Spec.Ledger.STS.Utxo as Shelley
import Shelley.Spec.Ledger.Tx (TxIn, ValidateScript)
import Shelley.Spec.Ledger.TxBody (unWdrl)
import Shelley.Spec.Ledger.UTxO
  ( UTxO (..),
    balance,
    txins,
    txouts,
    unUTxO,
  )

-- ============================================
-- The uninhabited type that marks the STS rule

data AlonzoUTXO era

-- ==========================================================

data UtxoPredicateFailure era
  = BadInputsUTxO
      !(Set (TxIn (Crypto era))) -- The bad transaction inputs
  | OutsideValidityIntervalUTxO
      !ValidityInterval -- transaction's validity interval
      !SlotNo -- current slot
  | MaxTxSizeUTxO
      !Integer -- the actual transaction size
      !Integer -- the max transaction size
  | InputSetEmptyUTxO
  | FeeTooSmallUTxO
      !Coin -- the minimum fee for this transaction
      !Coin -- the fee supplied in this transaction
  | ValueNotConservedUTxO
      !(Core.Value era) -- the Coin consumed by this transaction
      !(Core.Value era) -- the Coin produced by this transaction
  | WrongNetwork
      !Network -- the expected network id
      !(Set (Addr (Crypto era))) -- the set of addresses with incorrect network IDs
  | WrongNetworkWithdrawal
      !Network -- the expected network id
      !(Set (RewardAcnt (Crypto era))) -- the set of reward addresses with incorrect network IDs
  | OutputTooSmallUTxO
      ![Core.TxOut era] -- list of supplied transaction outputs that are too small
  | UpdateFailure (PredicateFailure (Core.EraRule "PPUP" era)) -- Subtransition Failures
  | OutputBootAddrAttrsTooBig
      ![Core.TxOut era] -- list of supplied bad transaction outputs
  | TriesToForgeADA
  | OutputTooBigUTxO
      ![Core.TxOut era] -- list of supplied bad transaction outputs
  | FeeNotBalancedUTxO
      !Coin -- balance computed
      !Coin -- the fee supplied in this transaction
  | ScriptsNotPaidUTxO
      !(UTxO era) -- The UTxO entries which have the wrong kind of script
  | ExUnitsTooSmallUTxO
      !ExUnits -- Max EXUnits from the protocol parameters
      !ExUnits -- EXUnits supplied
  deriving (Generic)

deriving stock instance
  ( Shelley.TransUTxOState Show era,
    Show (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Show (UtxoPredicateFailure era)

deriving stock instance
  ( Shelley.TransUTxOState Eq era,
    TransValue Eq era,
    Eq (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Eq (UtxoPredicateFailure era)

instance
  ( Shelley.TransUTxOState NoThunks era,
    NoThunks (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  NoThunks (UtxoPredicateFailure era)

-- ====================================

minfee ::
  ( HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices
  ) =>
  Core.PParams era ->
  Tx era ->
  Coin
minfee pp tx =
  ((txsize tx) <×> a)
    <+> b
    <+> (scriptfee (getField @"_prices" pp) (txExunits (txbody tx)))
  where
    a = Coin (fromIntegral (getField @"_minfeeA" pp))
    b = Coin (fromIntegral (getField @"_minfeeB" pp))

-- =======================================
-- feesOK is a predicate with 3 parts. Newly introduced in the
-- Alonzo era. We can think of as "Returning" True, if all 3
-- parts are True. As a TransitionRule it will return (), and
-- raise an error (rather than return)  if any of the 3 parts are False.

feesOK ::
  forall era.
  ( Core.Value era ~ Alonzo.Value (Crypto era),
    Core.TxOut era ~ Alonzo.TxOut era,
    ValidateScript era,
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices
  ) =>
  Core.PParams era ->
  Tx era ->
  UTxO era ->
  Rule (AlonzoUTXO era) 'Transition ()
feesOK pp tx (UTxO m) = do
  let txb = txbody tx
      fees = txinputs_fee txb
      utxoFees = eval (fees ◁ m) -- compute the domain restriction to those inputs where fees are paid
      bal = Val.coin (balance @era (UTxO utxoFees))
      nonNative txout = isNonNativeScriptAddress tx (getField @"address" (txout :: (TxOut era)))
  -- Part 1
  (bal >= txfee txb) ?! FeeTooSmallUTxO bal (txfee txb)
  -- Part 2
  (all (not . nonNative) utxoFees) ?! ScriptsNotPaidUTxO (UTxO (Map.filter nonNative utxoFees))
  -- Part 3
  (minfee pp tx <= txfee txb) ?! FeeNotBalancedUTxO (minfee pp tx) (txfee txb)
  pure ()

-- ================================================================

-- | The UTxO transition rule for the Alonzo eras.
utxoTransition ::
  forall era.
  ( ValidateScript era,
    Embed (Core.EraRule "PPUP" era) (AlonzoUTXO era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ StrictMaybe (Update era),
    -- We leave Core.PParams abstract
    UsesPParams era,
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_minUTxOValue" (Core.PParams era) Coin,
    HasField "_maxTxSize" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices,
    HasField "_maxTxExUnits" (Core.PParams era) ExUnits,
    -- We fix Core.Value, Core.TxBody, and Core.TxOut
    Core.Value era ~ Alonzo.Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era
  ) =>
  TransitionRule (AlonzoUTXO era)
utxoTransition = do
  TRC (Shelley.UtxoEnv slot pp stakepools genDelegs, u, tx) <- judgmentContext
  let Shelley.UTxOState utxo _deposits _fees ppup = u

  let txb = txbody tx

  inInterval slot (getField @"vldt" txb)
    ?! OutsideValidityIntervalUTxO (getField @"vldt" txb) slot

  txins @era txb /= Set.empty ?! InputSetEmptyUTxO

  feesOK pp tx utxo

  let minimumFee = minfee pp tx
      txFee = getField @"txfee" txb
  minimumFee <= txFee ?! FeeTooSmallUTxO minimumFee txFee

  eval (txins @era txb ⊆ dom utxo)
    ?! BadInputsUTxO (eval ((txins @era txb) ➖ (dom utxo)))

  ni <- liftSTS $ asks networkId
  let addrsWrongNetwork =
        filter
          (\a -> getNetwork a /= ni)
          (fmap (getField @"address") $ toList $ getField @"outputs" txb)
  null addrsWrongNetwork ?! WrongNetwork ni (Set.fromList addrsWrongNetwork)
  let wdrlsWrongNetwork =
        filter
          (\a -> getRwdNetwork a /= ni)
          (Map.keys . unWdrl . getField @"wdrls" $ txb)
  null wdrlsWrongNetwork
    ?! WrongNetworkWithdrawal
      ni
      (Set.fromList wdrlsWrongNetwork)

  let consumed_ = consumed pp utxo txb
      produced_ = Shelley.produced @era pp stakepools txb
  consumed_ == produced_ ?! ValueNotConservedUTxO consumed_ produced_

  -- process Protocol Parameter Update Proposals -- NOT SURE WHAT IS GOING On HERE
  _ppup' <-
    trans @(Core.EraRule "PPUP" era) $
      TRC (PPUPEnv slot pp genDelegs, ppup, txUpdates txb)

  -- Check that the mint field does not try to mint ADA. This is equivalent to
  -- the check `adaPolicy ∉ supp mint tx` in the spec.
  Val.coin (getField @"mint" txb) == Val.zero ?! TriesToForgeADA

  let outputs = Map.elems $ unUTxO (txouts @era txb)
      minUTxOValue = getField @"_minUTxOValue" pp
      outputsTooSmall =
        filter
          ( \out ->
              let v = getField @"value" out
               in not $
                    Val.pointwise
                      (>=)
                      v
                      (Val.inject $ scaledMinDeposit v minUTxOValue)
          )
          outputs
  null outputsTooSmall ?! OutputTooSmallUTxO outputsTooSmall

  let outputsTooBig =
        filter
          ( \out ->
              let v = getField @"value" out
               in (BSL.length . serialize) v > 4000
              -- TODO this is arbitrary, THERE IS SUPPOSEDLY A NEW
              -- PParams files that holds this what is it? --TODO fix this
          )
          outputs
  null outputsTooBig ?! OutputTooBigUTxO outputsTooBig

  -- Bootstrap (i.e. Byron) addresses have variable sized attributes in them.
  -- It is important to limit their overall size.
  let outputsAttrsTooBig =
        filter
          ( \out -> case getField @"address" out of
              AddrBootstrap addr -> bootstrapAddressAttrsSize addr > 64
              _ -> False
          )
          outputs
  null outputsAttrsTooBig ?! OutputBootAddrAttrsTooBig outputsAttrsTooBig

  let maxTxSize_ = fromIntegral (getField @"_maxTxSize" pp)
      txSize_ = txsize tx
  txSize_ <= maxTxSize_ ?! MaxTxSizeUTxO txSize_ maxTxSize_

  let maxTxEx = getField @"_maxTxExUnits" pp
  txExunits txb <= maxTxEx ?! ExUnitsTooSmallUTxO maxTxEx (txExunits txb)

  utxoS tx

utxoS :: Tx era -> TransitionRule (AlonzoUTXO era)
utxoS _tx = undefined

--------------------------------------------------------------------------------
-- AlonzoUTXO STS
--------------------------------------------------------------------------------

instance
  forall era.
  ( Era era,
    ValidateScript era,
    Embed (Core.EraRule "PPUP" era) (AlonzoUTXO era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ StrictMaybe (Update era),
    -- We leave Core.PParams abstract
    UsesPParams era,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_minUTxOValue" (Core.PParams era) Coin,
    HasField "_maxTxSize" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices,
    HasField "_maxTxExUnits" (Core.PParams era) ExUnits,
    -- We fix Core.Value, Core.TxBody, and Core.TxOut
    Core.Value era ~ Alonzo.Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era
  ) =>
  STS (AlonzoUTXO era)
  where
  type State (AlonzoUTXO era) = Shelley.UTxOState era
  type Signal (AlonzoUTXO era) = Tx era
  type
    Environment (AlonzoUTXO era) =
      Shelley.UtxoEnv era
  type BaseM (AlonzoUTXO era) = ShelleyBase
  type
    PredicateFailure (AlonzoUTXO era) =
      UtxoPredicateFailure era

  initialRules = []
  transitionRules = [utxoTransition]

instance
  ( Era era,
    STS (PPUP era),
    PredicateFailure (Core.EraRule "PPUP" era) ~ PpupPredicateFailure era
  ) =>
  Embed (PPUP era) (AlonzoUTXO era)
  where
  wrapFailed = UpdateFailure

--------------------------------------------------------------------------------
-- Serialisation
--------------------------------------------------------------------------------

instance
  ( Shelley.TransUTxOState ToCBOR era,
    ToCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  ToCBOR (UtxoPredicateFailure era)
  where
  toCBOR x = encode (encFail x)

encFail ::
  forall era.
  ( Shelley.TransUTxOState ToCBOR era,
    ToCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  UtxoPredicateFailure era ->
  Encode 'Open (UtxoPredicateFailure era)
encFail (BadInputsUTxO ins) = (Sum (BadInputsUTxO @era) 0 !> E encodeFoldable ins)
encFail (OutsideValidityIntervalUTxO a b) = (Sum OutsideValidityIntervalUTxO 1 !> To a !> To b)
encFail (MaxTxSizeUTxO a b) = (Sum MaxTxSizeUTxO 2 !> To a !> To b)
encFail (InputSetEmptyUTxO) = (Sum InputSetEmptyUTxO 3)
encFail (FeeTooSmallUTxO a b) = (Sum FeeTooSmallUTxO 4 !> To a !> To b)
encFail (ValueNotConservedUTxO a b) = (Sum (ValueNotConservedUTxO @era) 5 !> To a !> To b)
encFail (OutputTooSmallUTxO outs) = (Sum (OutputTooSmallUTxO @era) 6 !> E encodeFoldable outs)
encFail (UpdateFailure a) = (Sum (UpdateFailure @era) 7 !> To a)
encFail (WrongNetwork right wrongs) = (Sum (WrongNetwork @era) 8 !> To right !> E encodeFoldable wrongs)
encFail (WrongNetworkWithdrawal right wrongs) = (Sum (WrongNetworkWithdrawal @era) 9 !> To right !> E encodeFoldable wrongs)
encFail (OutputBootAddrAttrsTooBig outs) = (Sum (OutputBootAddrAttrsTooBig @era) 10 !> E encodeFoldable outs)
encFail (TriesToForgeADA) = (Sum TriesToForgeADA 11)
encFail (OutputTooBigUTxO outs) = (Sum (OutputTooBigUTxO @era) 12 !> E encodeFoldable outs)
encFail (FeeNotBalancedUTxO a b) = (Sum FeeNotBalancedUTxO 13 !> To a !> To b)
encFail (ScriptsNotPaidUTxO a) = (Sum ScriptsNotPaidUTxO 14 !> To a)
encFail (ExUnitsTooSmallUTxO a b) = (Sum ExUnitsTooSmallUTxO 15 !> To a !> To b)

decFail ::
  ( Shelley.TransUTxOState FromCBOR era,
    FromCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Word ->
  Decode 'Open (UtxoPredicateFailure era)
decFail 0 = SumD (BadInputsUTxO) <! D (decodeSet fromCBOR)
decFail 1 = SumD OutsideValidityIntervalUTxO <! From <! From
decFail 2 = SumD MaxTxSizeUTxO <! From <! From
decFail 3 = SumD InputSetEmptyUTxO
decFail 4 = SumD FeeTooSmallUTxO <! From <! From
decFail 5 = SumD (ValueNotConservedUTxO) <! From <! From
decFail 6 = SumD (OutputTooSmallUTxO) <! D (decodeList fromCBOR)
decFail 7 = SumD (UpdateFailure) <! From
decFail 8 = SumD (WrongNetwork) <! From <! D (decodeSet fromCBOR)
decFail 9 = SumD (WrongNetworkWithdrawal) <! From <! D (decodeSet fromCBOR)
decFail 10 = SumD (OutputBootAddrAttrsTooBig) <! D (decodeList fromCBOR)
decFail 11 = SumD TriesToForgeADA
decFail 12 = SumD (OutputTooBigUTxO) <! D (decodeList fromCBOR)
decFail 13 = SumD FeeNotBalancedUTxO <! From <! From
decFail 14 = SumD ScriptsNotPaidUTxO <! From
decFail 15 = SumD ExUnitsTooSmallUTxO <! From <! From
decFail n = Invalid n

instance
  ( Shelley.TransUTxOState FromCBOR era,
    FromCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  FromCBOR (UtxoPredicateFailure era)
  where
  fromCBOR = decode (Summands "UtxoPredicateFailure" decFail)
