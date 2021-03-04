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

module Cardano.Ledger.Alonzo.Rules.Utxo where

import Cardano.Binary (FromCBOR (..), ToCBOR (..), serialize)
import Cardano.Ledger.Alonzo.Rules.Utxos (UTXOS, UtxosPredicateFailure)
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices)
import Cardano.Ledger.Alonzo.Tx
  ( Tx (..),
    isNonNativeScriptAddress,
    minfee,
    txbody,
  )
import qualified Cardano.Ledger.Alonzo.Tx as Alonzo (Tx)
import Cardano.Ledger.Alonzo.TxBody
  ( TxOut (..),
  )
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo (TxBody, TxOut)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import qualified Cardano.Ledger.Mary.Value as Alonzo (Value)
import Cardano.Ledger.Shelley.Constraints
  ( UsesPParams,
  )
import Cardano.Ledger.ShelleyMA.Rules.Utxo (consumed, scaledMinDeposit)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..), inInterval)
import Cardano.Ledger.Val (coin, (<×>))
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
import Data.Coerce (coerce)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Int (Int64)
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
    networkId,
  )
import Shelley.Spec.Ledger.Coin
import qualified Shelley.Spec.Ledger.LedgerState as Shelley
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

-- | Compute an estimate of the size of storing one UTxO entry.
--
-- We need to estimate the size of storing 1 extra entry in the UTxO
-- @type UTxO = Map (TxIn (Crypto era)) (TxOut era)@
-- TxIn = (SafeHash,Word64), so sizeTxIn = sizeSafeHash + 8 bytes
-- So one extra entry adds ( sizeSafeHash + 8 + sizeTxOut + mapOverhead )
-- All this is computed by outputSize. Remember this is an estimate that
-- just needs to be proportional to the actual size.
outputSize :: Era era => TxOut era -> Int64
outputSize txout = sizeSafeHash + 8 + BSL.length (serialize txout) + mapOverhead
  where
    sizeSafeHash = 36
    mapOverhead = 14

-- ============================================

-- | The uninhabited type that marks the Alonzo UTxO rule
data AlonzoUTXO era

-- ==========================================================

data UtxoPredicateFailure era
  = -- | The bad transaction inputs
    BadInputsUTxO
      !(Set (TxIn (Crypto era)))
  | OutsideValidityIntervalUTxO
      !ValidityInterval
      -- ^ transaction's validity interval
      !SlotNo
      -- ^ current slot
  | MaxTxSizeUTxO
      !Integer
      -- ^ the actual transaction size
      !Integer
      -- ^ the max transaction size
  | InputSetEmptyUTxO
  | FeeTooSmallUTxO
      !Coin
      -- ^ the minimum fee for this transaction
      !Coin
      -- ^ the fee supplied in this transaction
  | ValueNotConservedUTxO
      !(Core.Value era)
      -- ^ the Coin consumed by this transaction
      !(Core.Value era)
      -- ^ the Coin produced by this transaction
  | -- | the set of addresses with incorrect network IDs
    WrongNetwork
      !Network -- the expected network id
      !(Set (Addr (Crypto era)))
  | WrongNetworkWithdrawal
      !Network
      -- ^ the expected network id
      !(Set (RewardAcnt (Crypto era)))
      -- ^ the set of reward addresses with incorrect network IDs
  | -- | list of supplied transaction outputs that are too small
    OutputTooSmallUTxO
      ![Core.TxOut era]
  | -- | Subtransition Failures
    UtxosFailure (PredicateFailure (Core.EraRule "UTXOS" era))
  | -- | list of supplied bad transaction outputs
    OutputBootAddrAttrsTooBig
      ![Core.TxOut era]
  | TriesToForgeADA
  | -- | list of supplied bad transaction outputs
    OutputTooBigUTxO
      ![Core.TxOut era]
  | FeeNotBalancedUTxO
      !Coin
      -- ^ balance computed
      !Coin
      -- ^ the fee supplied in this transaction
  | -- | The UTxO entries which have the wrong kind of script
    ScriptsNotPaidUTxO
      !(UTxO era)
  | ExUnitsTooSmallUTxO
      !ExUnits
      -- ^ Max EXUnits from the protocol parameters
      !ExUnits
      -- ^ EXUnits supplied
  | -- | The inputs marked for use as fees contain non-ADA tokens
    FeeContainsNonADA !(Core.Value era)
  deriving (Generic)

deriving stock instance
  ( Era era,
    Show (Core.Value era),
    Show (Core.TxOut era),
    Show (Core.TxBody era),
    Show (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  Show (UtxoPredicateFailure era)

deriving stock instance
  ( Eq (Core.Value era),
    Eq (Core.TxOut era),
    Eq (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  Eq (UtxoPredicateFailure era)

instance
  ( Era era,
    Shelley.TransUTxOState NoThunks era,
    NoThunks (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  NoThunks (UtxoPredicateFailure era)

-- | feesOK is a predicate with 4 parts:
--   - Check that the fee is greater than the minimum fee for the transaction
--   - The fee inputs do not belong to non-native script addresses
--   - The fee inputs are sufficient to cover the fee marked in the transaction
--   - The fee inputs do not contain any non-ADA part
--
--   As a TransitionRule it will return (), and raise an error (rather than
--   return) if any of the 4 parts are False.
feesOK ::
  forall era.
  ( Era era,
    ValidateScript era, -- isNonNativeScriptAddress
    Core.TxOut era ~ Alonzo.TxOut era, -- balance requires this,
    HasField "totExunits" (Core.Tx era) ExUnits, -- minfee requires this
    HasField
      "txinputs_fee" -- to get inputs to pay the fees
      (Core.TxBody era)
      (Set (TxIn (Crypto era))),
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices
  ) =>
  Core.PParams era ->
  Core.Tx era ->
  UTxO era ->
  Rule (AlonzoUTXO era) 'Transition ()
feesOK pp tx (UTxO m) = do
  let txb = getField @"body" tx
      theFee = getField @"txfee" txb -- Coin supplied to pay fees
      fees = getField @"txinputs_fee" txb -- Inputs allocated to pay theFee
      utxoFees = eval (fees ◁ m) -- restrict Utxo to those inputs we use to pay fees.
      bal = balance @era (UTxO utxoFees)
      nonNative txout = isNonNativeScriptAddress @era tx (getField @"address" txout)
      minimumFee = minfee @era pp tx
  -- Part 1
  (Val.coin bal >= theFee) ?! FeeNotBalancedUTxO (Val.coin bal) theFee
  -- Part 2
  not (any nonNative utxoFees) ?! ScriptsNotPaidUTxO (UTxO (Map.filter nonNative utxoFees))
  -- Part 3
  (minimumFee <= theFee) ?! FeeTooSmallUTxO minimumFee theFee
  -- Part 4
  Val.inject (Val.coin bal) == bal ?! FeeContainsNonADA bal
  pure ()

-- ================================================================

-- | The UTxO transition rule for the Alonzo eras.
utxoTransition ::
  forall era.
  ( Era era,
    ValidateScript era,
    -- instructions for calling UTXOS from AlonzoUTXO
    Embed (Core.EraRule "UTXOS" era) (AlonzoUTXO era),
    Environment (Core.EraRule "UTXOS" era) ~ Shelley.UtxoEnv era,
    State (Core.EraRule "UTXOS" era) ~ Shelley.UTxOState era,
    Signal (Core.EraRule "UTXOS" era) ~ Tx era,
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
    HasField "_adaPerUTxOByte" (Core.PParams era) Coin,
    -- We fix Core.Tx, Core.Value, Core.TxBody, and Core.TxOut
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Value era ~ Alonzo.Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Tx era ~ Alonzo.Tx era
  ) =>
  TransitionRule (AlonzoUTXO era)
utxoTransition = do
  TRC (Shelley.UtxoEnv slot pp stakepools _genDelegs, u, tx) <- judgmentContext
  let Shelley.UTxOState utxo _deposits _fees _ppup = u

  let txb = txbody tx

  inInterval slot (getField @"vldt" txb)
    ?! OutsideValidityIntervalUTxO (getField @"vldt" txb) slot

  not (Set.null (txins @era txb)) ?! InputSetEmptyUTxO

  feesOK pp tx utxo -- Generalizes the fee to small from earlier Era's
  eval (txins @era txb ⊆ dom utxo)
    ?! BadInputsUTxO (eval (txins @era txb ➖ dom utxo))

  let consumed_ = consumed pp utxo txb
      produced_ = Shelley.produced @era pp stakepools txb
  consumed_ == produced_ ?! ValueNotConservedUTxO consumed_ produced_

  -- Check that the mint field does not try to mint ADA. This is equivalent to
  -- the check `adaPolicy ∉ supp mint tx` in the spec.
  Val.coin (getField @"mint" txb) == Val.zero ?! TriesToForgeADA

  let outputs = Map.elems $ unUTxO (txouts @era txb)
      ok out =
        coin (getField @"value" out)
          >= (outputSize out <×> getField @"_adaPerUTxOByte" pp)
      outputsTooBig = filter (not . ok) outputs
  null outputsTooBig ?! OutputTooBigUTxO outputsTooBig

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

  -- TODO remove this?
  -- It does not appear in the Alonzo specification. SHOULD IT STAY?
  let minUTxOValue = getField @"_minUTxOValue" pp
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

  let maxTxSize_ = fromIntegral (getField @"_maxTxSize" pp)
      txSize_ = getField @"txsize" tx
  txSize_ <= maxTxSize_ ?! MaxTxSizeUTxO txSize_ maxTxSize_

  let maxTxEx = getField @"_maxTxExUnits" pp
      totExunits = getField @"totExunits" tx
  totExunits <= maxTxEx ?! ExUnitsTooSmallUTxO maxTxEx totExunits

  -- This does not appear in the Alonzo specification. But the test should be in every Era.
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

  trans @(Core.EraRule "UTXOS" era) =<< coerce <$> judgmentContext

--------------------------------------------------------------------------------
-- AlonzoUTXO STS
--------------------------------------------------------------------------------

instance
  forall era.
  ( ValidateScript era,
    -- Instructions needed to call the UTXOS transition from this one.
    Embed (Core.EraRule "UTXOS" era) (AlonzoUTXO era),
    Environment (Core.EraRule "UTXOS" era) ~ Shelley.UtxoEnv era,
    State (Core.EraRule "UTXOS" era) ~ Shelley.UTxOState era,
    Signal (Core.EraRule "UTXOS" era) ~ Tx era,
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
    HasField "_adaPerUTxOByte" (Core.PParams era) Coin,
    -- We fix Core.Value, Core.TxBody, and Core.TxOut
    Core.Value era ~ Alonzo.Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Tx era ~ Alonzo.Tx era
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
    STS (UTXOS era),
    PredicateFailure (Core.EraRule "UTXOS" era) ~ UtxosPredicateFailure era
  ) =>
  Embed (UTXOS era) (AlonzoUTXO era)
  where
  wrapFailed = UtxosFailure

--------------------------------------------------------------------------------
-- Serialisation
--------------------------------------------------------------------------------

instance
  ( Typeable era,
    Era era,
    ToCBOR (Core.TxOut era),
    ToCBOR (Core.Value era),
    ToCBOR (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  ToCBOR (UtxoPredicateFailure era)
  where
  toCBOR x = encode (encFail x)

encFail ::
  forall era.
  ( Era era,
    ToCBOR (Core.TxOut era),
    ToCBOR (Core.Value era),
    ToCBOR (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  UtxoPredicateFailure era ->
  Encode 'Open (UtxoPredicateFailure era)
encFail (BadInputsUTxO ins) =
  Sum (BadInputsUTxO @era) 0 !> E encodeFoldable ins
encFail (OutsideValidityIntervalUTxO a b) =
  Sum OutsideValidityIntervalUTxO 1 !> To a !> To b
encFail (MaxTxSizeUTxO a b) =
  Sum MaxTxSizeUTxO 2 !> To a !> To b
encFail (InputSetEmptyUTxO) =
  Sum InputSetEmptyUTxO 3
encFail (FeeTooSmallUTxO a b) =
  Sum FeeTooSmallUTxO 4 !> To a !> To b
encFail (ValueNotConservedUTxO a b) =
  Sum (ValueNotConservedUTxO @era) 5 !> To a !> To b
encFail (OutputTooSmallUTxO outs) =
  Sum (OutputTooSmallUTxO @era) 6 !> E encodeFoldable outs
encFail (UtxosFailure a) =
  Sum (UtxosFailure @era) 7 !> To a
encFail (WrongNetwork right wrongs) =
  Sum (WrongNetwork @era) 8 !> To right !> E encodeFoldable wrongs
encFail (WrongNetworkWithdrawal right wrongs) =
  Sum (WrongNetworkWithdrawal @era) 9 !> To right !> E encodeFoldable wrongs
encFail (OutputBootAddrAttrsTooBig outs) =
  Sum (OutputBootAddrAttrsTooBig @era) 10 !> E encodeFoldable outs
encFail (TriesToForgeADA) =
  Sum TriesToForgeADA 11
encFail (OutputTooBigUTxO outs) =
  Sum (OutputTooBigUTxO @era) 12 !> E encodeFoldable outs
encFail (FeeNotBalancedUTxO a b) =
  Sum FeeNotBalancedUTxO 13 !> To a !> To b
encFail (ScriptsNotPaidUTxO a) =
  Sum ScriptsNotPaidUTxO 14 !> To a
encFail (ExUnitsTooSmallUTxO a b) =
  Sum ExUnitsTooSmallUTxO 15 !> To a !> To b
encFail (FeeContainsNonADA a) =
  Sum FeeContainsNonADA 16 !> To a

decFail ::
  ( Era era,
    FromCBOR (Core.TxOut era),
    FromCBOR (Core.Value era),
    FromCBOR (PredicateFailure (Core.EraRule "UTXOS" era))
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
decFail 7 = SumD (UtxosFailure) <! From
decFail 8 = SumD (WrongNetwork) <! From <! D (decodeSet fromCBOR)
decFail 9 = SumD (WrongNetworkWithdrawal) <! From <! D (decodeSet fromCBOR)
decFail 10 = SumD (OutputBootAddrAttrsTooBig) <! D (decodeList fromCBOR)
decFail 11 = SumD TriesToForgeADA
decFail 12 = SumD (OutputTooBigUTxO) <! D (decodeList fromCBOR)
decFail 13 = SumD FeeNotBalancedUTxO <! From <! From
decFail 14 = SumD ScriptsNotPaidUTxO <! From
decFail 15 = SumD ExUnitsTooSmallUTxO <! From <! From
decFail 16 = SumD FeeContainsNonADA <! From
decFail n = Invalid n

instance
  ( Era era,
    FromCBOR (Core.TxOut era),
    FromCBOR (Core.Value era),
    FromCBOR (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  FromCBOR (UtxoPredicateFailure era)
  where
  fromCBOR = decode (Summands "UtxoPredicateFailure" decFail)
