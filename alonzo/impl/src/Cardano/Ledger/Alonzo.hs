{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo where

import Cardano.Ledger.Alonzo.Data (AuxiliaryData)
import Cardano.Ledger.Alonzo.PParams (PParams, PParams' (..), PParamsUpdate, updatePParams)
import qualified Cardano.Ledger.Alonzo.Rules.Utxo as Alonzo (AlonzoUTXO)
import qualified Cardano.Ledger.Alonzo.Rules.Utxos as Alonzo (UTXOS)
import qualified Cardano.Ledger.Alonzo.Rules.Utxow as Alonzo (AlonzoUTXOW)
import Cardano.Ledger.Alonzo.Scripts (Script)
import Cardano.Ledger.Alonzo.Tx (Tx)
import Cardano.Ledger.Alonzo.TxBody (TxBody, TxOut)
import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash (..), ValidateAuxiliaryData (..))
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Era
import Cardano.Ledger.Mary.Value (Value)
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.Constraints
  ( UsesPParams (..),
    UsesTxOut (..),
    UsesValue,
  )
import Control.State.Transition.Extended (STUB)
import qualified Control.State.Transition.Extended as STS
import Data.Typeable (Typeable)
import qualified Shelley.Spec.Ledger.API as API
import qualified Shelley.Spec.Ledger.BaseTypes as Shelley
import qualified Shelley.Spec.Ledger.STS.Bbody as STS
import qualified Shelley.Spec.Ledger.STS.Bbody as Shelley
import qualified Shelley.Spec.Ledger.STS.Epoch as Shelley
import qualified Shelley.Spec.Ledger.STS.Mir as Shelley
import qualified Shelley.Spec.Ledger.STS.Newpp as Shelley
import qualified Shelley.Spec.Ledger.STS.Ocert as Shelley
import qualified Shelley.Spec.Ledger.STS.Overlay as Shelley
import qualified Shelley.Spec.Ledger.STS.Rupd as Shelley
import qualified Shelley.Spec.Ledger.STS.Snap as Shelley
import qualified Shelley.Spec.Ledger.STS.Tick as Shelley
import qualified Shelley.Spec.Ledger.STS.Upec as Shelley
import qualified Shelley.Spec.Ledger.Tx as Shelley

-- | The Alonzo era
data AlonzoEra c

instance API.PraosCrypto c => API.ApplyTx (AlonzoEra c)

instance API.PraosCrypto c => API.ApplyBlock (AlonzoEra c)

instance API.PraosCrypto c => API.GetLedgerView (AlonzoEra c)

instance
  (CC.Crypto c) =>
  Shelley.ValidateScript (AlonzoEra c)
  where
  validateScript = error "TODO: implement validateScript"
  hashScript = error "TODO: implement hashScript"

instance
  ( CC.Crypto c
  ) =>
  API.CanStartFromGenesis (AlonzoEra c)
  where
  -- type AdditionalGenesisConfig era = ()
  -- initialState :: ShelleyGenesis era -> AdditionalGenesisConfig era -> NewEpochState era
  initialState _ _ = error "TODO: implement initialState"

instance CC.Crypto c => UsesTxOut (AlonzoEra c) where
  -- makeTxOut :: Proxy era -> Addr (Crypto era) -> Value era -> TxOut era
  makeTxOut = error "TODO: implement makeTxOut"

instance
  (CC.Crypto c) =>
  Era (AlonzoEra c)
  where
  type Crypto (AlonzoEra c) = c

type instance Core.TxOut (AlonzoEra c) = TxOut (AlonzoEra c)

type instance Core.TxBody (AlonzoEra c) = TxBody (AlonzoEra c)

type instance Core.TxOut (AlonzoEra c) = TxOut (AlonzoEra c)

type instance Core.Value (AlonzoEra c) = Value c

type instance Core.Script (AlonzoEra c) = Script (AlonzoEra c)

type instance Core.AuxiliaryData (AlonzoEra c) = AuxiliaryData (AlonzoEra c)

type instance Core.PParams (AlonzoEra c) = PParams (AlonzoEra c)

type instance Core.Tx (AlonzoEra c) = Tx (AlonzoEra c)

instance CC.Crypto c => UsesValue (AlonzoEra c)

instance
  (CC.Crypto c) =>
  UsesPParams (AlonzoEra c)
  where
  type
    PParamsDelta (AlonzoEra c) =
      PParamsUpdate (AlonzoEra c)

  mergePPUpdates _ = updatePParams

instance CC.Crypto c => ValidateAuxiliaryData (AlonzoEra c) c where
  hashAuxiliaryData x = AuxiliaryDataHash (hashAnnotated x)
  validateAuxiliaryData = error ("NO validateAuxiliaryData yet.") -- TODO Fill this in

instance API.PraosCrypto c => API.ShelleyBasedEra (AlonzoEra c)

-------------------------------------------------------------------------------
-- Era Mapping
-------------------------------------------------------------------------------

-- These rules are new or changed in Alonzo

type instance Core.EraRule "UTXOS" (AlonzoEra c) = Alonzo.UTXOS (AlonzoEra c)

type instance Core.EraRule "UTXO" (AlonzoEra c) = Alonzo.AlonzoUTXO (AlonzoEra c)

type instance Core.EraRule "UTXOW" (AlonzoEra c) = Alonzo.AlonzoUTXOW (AlonzoEra c)

type LEDGERSTUB c =
  STUB
    (API.LedgerEnv (AlonzoEra c))
    (API.UTxOState (AlonzoEra c), API.DPState c)
    (API.Tx (AlonzoEra c))
    ()
    Shelley.ShelleyBase

instance Typeable c => STS.Embed (LEDGERSTUB c) (API.LEDGERS (AlonzoEra c)) where
  wrapFailed = error "TODO: implement LEDGER rule"

type instance Core.EraRule "LEDGER" (AlonzoEra c) = LEDGERSTUB c

type instance
  Core.EraRule "BBODY" (AlonzoEra c) =
    STUB
      (Shelley.BbodyEnv (AlonzoEra c))
      (STS.BbodyState (AlonzoEra c))
      (API.Block (AlonzoEra c))
      ()
      Shelley.ShelleyBase

-- Rules inherited from Shelley

type instance Core.EraRule "DELEG" (AlonzoEra c) = API.DELEG (AlonzoEra c)

type instance Core.EraRule "DELEGS" (AlonzoEra c) = API.DELEGS (AlonzoEra c)

type instance Core.EraRule "DELPL" (AlonzoEra c) = API.DELPL (AlonzoEra c)

type instance Core.EraRule "EPOCH" (AlonzoEra c) = Shelley.EPOCH (AlonzoEra c)

type instance Core.EraRule "LEDGERS" (AlonzoEra c) = API.LEDGERS (AlonzoEra c)

type instance Core.EraRule "MIR" (AlonzoEra c) = Shelley.MIR (AlonzoEra c)

type instance Core.EraRule "NEWEPOCH" (AlonzoEra c) = API.NEWEPOCH (AlonzoEra c)

type instance Core.EraRule "NEWPP" (AlonzoEra c) = Shelley.NEWPP (AlonzoEra c)

type instance Core.EraRule "OCERT" (AlonzoEra c) = Shelley.OCERT (AlonzoEra c)

type instance Core.EraRule "OVERLAY" (AlonzoEra c) = Shelley.OVERLAY (AlonzoEra c)

type instance Core.EraRule "POOL" (AlonzoEra c) = API.POOL (AlonzoEra c)

type instance Core.EraRule "POOLREAP" (AlonzoEra c) = API.POOLREAP (AlonzoEra c)

type instance Core.EraRule "PPUP" (AlonzoEra c) = API.PPUP (AlonzoEra c)

type instance Core.EraRule "RUPD" (AlonzoEra c) = Shelley.RUPD (AlonzoEra c)

type instance Core.EraRule "SNAP" (AlonzoEra c) = Shelley.SNAP (AlonzoEra c)

type instance Core.EraRule "TICK" (AlonzoEra c) = Shelley.TICK (AlonzoEra c)

type instance Core.EraRule "TICKF" (AlonzoEra c) = Shelley.TICKF (AlonzoEra c)

type instance Core.EraRule "TICKN" (AlonzoEra _c) = API.TICKN

type instance Core.EraRule "UPEC" (AlonzoEra c) = Shelley.UPEC (AlonzoEra c)
