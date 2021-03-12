{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.ShelleyMA where

import Cardano.Ledger.AuxiliaryData
  ( AuxiliaryDataHash (..),
    ValidateAuxiliaryData (..),
  )
import Cardano.Ledger.Compactible (Compactible)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Mary.Value (Value, policies, policyID)
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.Constraints
  ( UsesPParams (..),
    UsesTxBody,
    UsesTxOut (..),
    UsesValue,
  )
import Cardano.Ledger.ShelleyMA.AuxiliaryData
  ( AuxiliaryData,
    pattern AuxiliaryData,
  )
import Cardano.Ledger.ShelleyMA.Timelocks
  ( Timelock (..),
    ValidityInterval,
    validateTimelock,
  )
import Cardano.Ledger.ShelleyMA.TxBody (TxBody)
import Cardano.Ledger.Val (Val)
import Control.DeepSeq (deepseq)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Records (HasField (..))
import Shelley.Spec.Ledger.Coin (Coin)
import Shelley.Spec.Ledger.Metadata (validMetadatum)
import qualified Shelley.Spec.Ledger.PParams as Shelley
import Shelley.Spec.Ledger.Scripts (ScriptHash)
import Shelley.Spec.Ledger.Tx
  ( Tx,
    TxOut (..),
    ValidateScript (..),
    nativeMultiSigTag,
  )

-- | The Shelley Mary/Allegra eras
--   The uninhabited type that indexes both the Mary and Allegra Eras.
data ShelleyMAEra (ma :: MaryOrAllegra) c

-- Both eras are implemented within the same codebase, matching the formal
-- specification. They differ only in the @value@ type. Due to some annoying
-- issues with 'Coin' and 'Value' being of different kinds, we don't parametrise
-- over the value but instead over a closed kind 'MaryOrAllegra'. But this
-- should be transparent to the user.
data MaryOrAllegra = Mary | Allegra

-- | The MAClass provides a method and a type, which implement the differences
--   between the Mary and Allegra instances
class
  ( Compactible (MAValue x c),
    Show (MAValue x c),
    Val (MAValue x c),
    Typeable x,
    CryptoClass.Crypto c
  ) =>
  MAClass (x :: MaryOrAllegra) c
  where
  type MAValue (x :: MaryOrAllegra) c :: Type
  getScriptHash :: Proxy x -> MAValue x c -> (Set.Set (ScriptHash c))

instance CryptoClass.Crypto c => MAClass 'Mary c where
  type MAValue 'Mary c = Value c
  getScriptHash Proxy x = Set.map policyID (policies x)

instance CryptoClass.Crypto c => MAClass 'Allegra c where
  type MAValue 'Allegra c = Coin
  getScriptHash _ _ = Set.empty

-- | The actual Mary and Allegra instances, rolled into one, the MAClass superclass
--   provides the era-specific code for where they differ.
instance
  forall c (ma :: MaryOrAllegra).
  (MAClass ma c) =>
  Era (ShelleyMAEra ma c)
  where
  type Crypto (ShelleyMAEra ma c) = c

instance CryptoClass.Crypto c => UsesValue (ShelleyMAEra 'Mary c)

instance CryptoClass.Crypto c => UsesValue (ShelleyMAEra 'Allegra c)

instance CryptoClass.Crypto c => UsesTxOut (ShelleyMAEra 'Mary c) where
  makeTxOut _ a v = TxOut a v

instance CryptoClass.Crypto c => UsesTxOut (ShelleyMAEra 'Allegra c) where
  makeTxOut _ a v = TxOut a v

instance
  (MAClass ma c) =>
  UsesPParams (ShelleyMAEra ma c)
  where
  type
    PParamsDelta (ShelleyMAEra ma c) =
      Shelley.PParamsUpdate (ShelleyMAEra ma c)

  mergePPUpdates _ = Shelley.updatePParams

--------------------------------------------------------------------------------
-- Core instances
--------------------------------------------------------------------------------

type instance Core.Value (ShelleyMAEra m c) = MAValue m c

type instance
  Core.TxOut (ShelleyMAEra (ma :: MaryOrAllegra) c) =
    TxOut (ShelleyMAEra ma c)

type instance
  Core.TxBody (ShelleyMAEra (ma :: MaryOrAllegra) c) =
    TxBody (ShelleyMAEra ma c)

type instance
  Core.Script (ShelleyMAEra (_ma :: MaryOrAllegra) c) =
    Timelock c

type instance
  Core.AuxiliaryData (ShelleyMAEra (ma :: MaryOrAllegra) c) =
    AuxiliaryData (ShelleyMAEra (ma :: MaryOrAllegra) c)

type instance
  Core.PParams (ShelleyMAEra (ma :: MaryOrAllegra) c) =
    Shelley.PParams (ShelleyMAEra (ma :: MaryOrAllegra) c)

type instance
  Core.Tx (ShelleyMAEra (ma :: MaryOrAllegra) c) =
    Tx (ShelleyMAEra (ma :: MaryOrAllegra) c)

--------------------------------------------------------------------------------
-- Ledger data instances
--------------------------------------------------------------------------------

-- since timelock scripts are a strict backwards compatible extension of
--  Multisig scripts, we can use the same 'scriptPrefixTag' tag here as
-- we did for the ValidateScript instance in Multisig

instance
  ( CryptoClass.Crypto c,
    UsesTxBody (ShelleyMAEra ma c),
    Core.AnnotatedData (Core.AuxiliaryData (ShelleyMAEra ma c)),
    (HasField "vldt" (Core.TxBody (ShelleyMAEra ma c)) ValidityInterval)
  ) =>
  ValidateScript (ShelleyMAEra ma c)
  where
  scriptPrefixTag _proxy = nativeMultiSigTag -- "\x00"
  validateScript s tx = validateTimelock s tx

-- Uses the default instance of hashScript

instance
  ( CryptoClass.Crypto c,
    Core.AnnotatedData (Core.Script (ShelleyMAEra ma c))
  ) =>
  ValidateAuxiliaryData (ShelleyMAEra (ma :: MaryOrAllegra) c) c
  where
  validateAuxiliaryData (AuxiliaryData md as) = deepseq as $ all validMetadatum md
  hashAuxiliaryData aux = AuxiliaryDataHash (hashAnnotated aux)

instance
  forall ma c.
  MAClass ma c =>
  HasField "minted" (TxBody (ShelleyMAEra (ma :: MaryOrAllegra) c)) (Set.Set (ScriptHash c))
  where
  getField x = getScriptHash (Proxy @ma) (getField @"mint" x)
