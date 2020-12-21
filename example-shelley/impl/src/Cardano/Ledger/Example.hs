{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This is a stub example of a Shelley era, designed for testing,
-- prototyping, and demo purposes.
module Cardano.Ledger.Example where

import Cardano.Ledger.AuxiliaryData
  ( AuxiliaryDataHash (..),
    ValidateAuxiliaryData (..),
  )
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.SafeHash (EraIndependentAuxiliaryData, makeHashWithExplicitProxys)
import Cardano.Ledger.Shelley.Constraints (UsesPParams (..), UsesTxOut (..), UsesValue)
import Data.Proxy
import Shelley.Spec.Ledger.Coin (Coin)
import Shelley.Spec.Ledger.Metadata (Metadata (Metadata), validMetadatum)
import Shelley.Spec.Ledger.Scripts (MultiSig)
import Shelley.Spec.Ledger.PParams as Shelley
import Shelley.Spec.Ledger.Tx
  ( ValidateScript (hashScript, validateScript),
    hashMultiSigScript,
    validateNativeMultiSigScript,
  )
import Shelley.Spec.Ledger.API
  ( ApplyBlock,
    ApplyTx,
    GetLedgerView,
    PraosCrypto,
    ShelleyBasedEra,
    TxOut (..)
  )

import Shelley.Spec.Ledger.TxBody (TxBody (..))

import Shelley.Spec.Ledger.STS.Bbody (BBODY)
import Shelley.Spec.Ledger.STS.Deleg (DELEG)
import Shelley.Spec.Ledger.STS.Delegs (DELEGS)
import Shelley.Spec.Ledger.STS.Delpl (DELPL)
import Shelley.Spec.Ledger.STS.Epoch (EPOCH)
import Shelley.Spec.Ledger.STS.Ledger (LEDGER)
import Shelley.Spec.Ledger.STS.Ledgers (LEDGERS)
import Shelley.Spec.Ledger.STS.Mir (MIR)
import Shelley.Spec.Ledger.STS.NewEpoch (NEWEPOCH)
import Shelley.Spec.Ledger.STS.Newpp (NEWPP)
import Shelley.Spec.Ledger.STS.Ocert (OCERT)
import Shelley.Spec.Ledger.STS.Overlay (OVERLAY)
import Shelley.Spec.Ledger.STS.Pool (POOL)
import Shelley.Spec.Ledger.STS.PoolReap (POOLREAP)
import Shelley.Spec.Ledger.STS.Ppup (PPUP)
import Shelley.Spec.Ledger.STS.Rupd (RUPD)
import Shelley.Spec.Ledger.STS.Snap (SNAP)
import Shelley.Spec.Ledger.STS.Tickn (TICKN)
import Shelley.Spec.Ledger.STS.Tick (TICK, TICKF)
import Shelley.Spec.Ledger.STS.Upec (UPEC)
import Shelley.Spec.Ledger.STS.Utxo (UTXO)
import Shelley.Spec.Ledger.STS.Utxow (UTXOW)

data ExampleEra c

instance CryptoClass.Crypto c => Era (ExampleEra c) where
  type Crypto (ExampleEra c) = c

instance CryptoClass.Crypto c => UsesValue (ExampleEra c)

instance CryptoClass.Crypto c => UsesTxOut (ExampleEra c) where
  makeTxOut _ a v = TxOut a v

--------------------------------------------------------------------------------
-- Core instances
--------------------------------------------------------------------------------

type instance Core.Value (ExampleEra _c) = Coin

type instance Core.TxBody (ExampleEra c) = TxBody (ExampleEra c)

type instance Core.TxOut (ExampleEra c) = TxOut (ExampleEra c)

type instance Core.Script (ExampleEra c) = MultiSig c

type instance Core.AuxiliaryData (ExampleEra c) = Metadata

type instance Core.PParams (ExampleEra c) = Shelley.PParams (ExampleEra c)

--------------------------------------------------------------------------------
-- Ledger data instances
--------------------------------------------------------------------------------

instance
  (CryptoClass.Crypto c) =>
  UsesPParams (ExampleEra c)
  where
  type
    PParamsDelta (ExampleEra c) =
      Shelley.PParamsUpdate (ExampleEra c)

  mergePPUpdates _ = Shelley.updatePParams

instance
  (CryptoClass.Crypto c) =>
  ValidateScript (ExampleEra c)
  where
  validateScript = validateNativeMultiSigScript
  hashScript = hashMultiSigScript

instance CryptoClass.Crypto c => ValidateAuxiliaryData (ExampleEra c) where
  hashAuxiliaryData metadata = AuxiliaryDataHash (makeHashWithExplicitProxys (Proxy @c) index metadata)
    where
      index = Proxy @EraIndependentAuxiliaryData
  validateAuxiliaryData (Metadata m) = all validMetadatum m

instance PraosCrypto c => ApplyTx (ExampleEra c)
instance PraosCrypto c => ApplyBlock (ExampleEra c)
instance PraosCrypto c => GetLedgerView (ExampleEra c)
instance PraosCrypto c => ShelleyBasedEra (ExampleEra c)

-- These rules are all inherited from Shelley
-- The types on the right are all instances of class STS, ultimately defined in Control.State.Transition.Extended
type instance Core.EraRule "BBODY" (ExampleEra c) = BBODY (ExampleEra c) -- Block body
type instance Core.EraRule "DELEG" (ExampleEra c) = DELEG (ExampleEra c)
type instance Core.EraRule "DELEGS" (ExampleEra c) = DELEGS (ExampleEra c)
type instance Core.EraRule "DELPL" (ExampleEra c) = DELPL (ExampleEra c)
type instance Core.EraRule "EPOCH" (ExampleEra c) = EPOCH (ExampleEra c)
type instance Core.EraRule "LEDGER" (ExampleEra c) = LEDGER (ExampleEra c)
type instance Core.EraRule "LEDGERS" (ExampleEra c) = LEDGERS (ExampleEra c)
type instance Core.EraRule "MIR" (ExampleEra c) = MIR (ExampleEra c)
type instance Core.EraRule "NEWEPOCH" (ExampleEra c) = NEWEPOCH (ExampleEra c)
type instance Core.EraRule "NEWPP" (ExampleEra c) = NEWPP (ExampleEra c)
type instance Core.EraRule "OCERT" (ExampleEra c) = OCERT (ExampleEra c)
type instance Core.EraRule "OVERLAY" (ExampleEra c) = OVERLAY (ExampleEra c)
type instance Core.EraRule "POOL" (ExampleEra c) = POOL (ExampleEra c)
type instance Core.EraRule "POOLREAP" (ExampleEra c) = POOLREAP (ExampleEra c)
type instance Core.EraRule "PPUP" (ExampleEra c) = PPUP (ExampleEra c)
type instance Core.EraRule "RUPD" (ExampleEra c) = RUPD (ExampleEra c)
type instance Core.EraRule "SNAP" (ExampleEra c) = SNAP (ExampleEra c)
type instance Core.EraRule "TICK" (ExampleEra c) = TICK (ExampleEra c)
type instance Core.EraRule "TICKF" (ExampleEra c) = TICKF (ExampleEra c)
type instance Core.EraRule "TICKN" (ExampleEra _c) = TICKN
type instance Core.EraRule "UPEC" (ExampleEra c) = UPEC (ExampleEra c)
type instance Core.EraRule "UTXO" (ExampleEra c) = UTXO (ExampleEra c)
type instance Core.EraRule "UTXOW" (ExampleEra c) = UTXOW (ExampleEra c)
