{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo.Rules.Utxos where

import Cardano.Ledger.Alonzo.Language (Language)
import Cardano.Ledger.Alonzo.Scripts (Script)
import Cardano.Ledger.Alonzo.Tx
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Shelley.Constraints
import qualified Cardano.Ledger.Val as Val
import Control.Iterate.SetAlgebra (eval, (∪), (⋪), (◁))
import Control.State.Transition.Extended
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks)
import Shelley.Spec.Ledger.BaseTypes (ShelleyBase, StrictMaybe (..), strictMaybeToMaybe)
import Shelley.Spec.Ledger.Coin (Coin)
import Shelley.Spec.Ledger.LedgerState
import qualified Shelley.Spec.Ledger.LedgerState as Shelley
import Shelley.Spec.Ledger.PParams (Update)
import Shelley.Spec.Ledger.STS.Ppup (PPUP, PPUPEnv (..), PpupPredicateFailure)
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.TxBody (DCert, TxIn (..), Wdrl)
import Shelley.Spec.Ledger.UTxO (balance, totalDeposits)

--------------------------------------------------------------------------------
-- The UTXOS transition system
--------------------------------------------------------------------------------

data UTXOS era

instance
  forall era.
  ( Era era,
    UsesAuxiliary era,
    UsesTxBody era,
    UsesTxOut era,
    UsesValue era,
    UsesPParams era,
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Core.Script era ~ Script era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.TxBody era ~ Alonzo.TxBody era,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era)))
  ) =>
  STS (UTXOS era)
  where
  type BaseM (UTXOS era) = ShelleyBase
  type Environment (UTXOS era) = UtxoEnv era
  type State (UTXOS era) = UTxOState era
  type Signal (UTXOS era) = Tx era
  type PredicateFailure (UTXOS era) = UtxosPredicateFailure era

  transitionRules = [utxosTransition]

utxosTransition ::
  forall era.
  ( UsesTxOut era,
    Core.Script era ~ Script era,
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Core.TxOut era ~ Alonzo.TxOut era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era))),
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era))
  ) =>
  TransitionRule (UTXOS era)
utxosTransition =
  judgmentContext >>= \(TRC (UtxoEnv _ pp _ _, UTxOState utxo _ _ _, tx)) ->
    let sLst = collectNNScriptInputs pp tx utxo
        scriptEvalResult = evalScripts @era sLst
     in if scriptEvalResult
          then scriptsValidateTransition
          else scriptsNotValidateTransition

scriptsValidateTransition ::
  forall era.
  ( UsesTxOut era,
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Core.TxOut era ~ Alonzo.TxOut era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin
  ) =>
  TransitionRule (UTXOS era)
scriptsValidateTransition = do
  TRC
    ( UtxoEnv slot pp poolParams genDelegs,
      UTxOState utxo deposited fees pup,
      tx
      ) <-
    judgmentContext
  let txb = txbody tx
      refunded = keyRefunds pp txb
      depositChange =
        ( totalDeposits
            pp
            poolParams
            (toList $ getField @"certs" txb)
        )
          Val.<-> refunded
  getField @"isValidating" tx == IsValidating True
    ?! ValidationTagMismatch (getField @"isValidating" tx)
  pup' <-
    trans @(Core.EraRule "PPUP" era) $
      TRC
        (PPUPEnv slot pp genDelegs, pup, strictMaybeToMaybe $ getField @"update" txb)
  pure $
    UTxOState
      { _utxo = eval ((txins @era txb ⋪ utxo) ∪ txouts @era txb),
        _deposited = deposited <> depositChange,
        _fees = fees <> getField @"txfee" txb,
        _ppups = pup'
      }

scriptsNotValidateTransition ::
  forall era.
  ( UsesTxOut era,
    HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era)))
  ) =>
  TransitionRule (UTXOS era)
scriptsNotValidateTransition = do
  TRC (_, us@(UTxOState utxo _ fees _), tx) <- judgmentContext
  let txb = txbody tx
  getField @"isValidating" tx == IsValidating False
    ?! ValidationTagMismatch (getField @"isValidating" tx)
  pure $
    us
      { _utxo = eval (getField @"txinputs_fee" txb ⋪ utxo),
        _fees = fees <> Val.coin (balance @era (eval (getField @"txinputs_fee" txb ◁ utxo)))
      }

data UtxosPredicateFailure era
  = -- | The 'isValidating' tag on the transaction is incorrect. The tag given
    --   here is that provided on the transaction (whereas evaluation of the
    --   scripts gives the opposite.)
    ValidationTagMismatch IsValidating
  | UpdateFailure (PredicateFailure (Core.EraRule "PPUP" era))
  deriving
    (Generic)

deriving stock instance
  ( Shelley.TransUTxOState Show era,
    TransValue Show era,
    Show (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Show (UtxosPredicateFailure era)

deriving stock instance
  ( Shelley.TransUTxOState Eq era,
    TransValue Eq era,
    Eq (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Eq (UtxosPredicateFailure era)

instance
  ( Shelley.TransUTxOState NoThunks era,
    NoThunks (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  NoThunks (UtxosPredicateFailure era)

instance
  ( Era era,
    STS (PPUP era),
    PredicateFailure (Core.EraRule "PPUP" era) ~ PpupPredicateFailure era
  ) =>
  Embed (PPUP era) (UTXOS era)
  where
  wrapFailed = UpdateFailure
