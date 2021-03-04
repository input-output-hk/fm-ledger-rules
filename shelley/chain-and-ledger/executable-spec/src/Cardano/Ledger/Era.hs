{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | Support for multiple (Shelley-based) eras in the ledger.
module Cardano.Ledger.Era
  ( Era,
    Crypto,
    PreviousEra,
    TranslationContext,
    TranslateEra (..),
    translateEra',
    translateEraMaybe,
    WellFormed,
  )
where

-- imports for the WellFormed constraint

import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash)
import Cardano.Ledger.Compactible (Compactible)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.SafeHash
  ( EraIndependentAuxiliaryData,
    EraIndependentTxBody,
    HashAnnotated (..),
  )
import Cardano.Ledger.Val (Val)
import Control.Monad.Except (Except, runExcept)
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import GHC.Records (HasField (..))
import Shelley.Spec.Ledger.Address (Addr)
import Shelley.Spec.Ledger.Address.Bootstrap (BootstrapWitness)
import Shelley.Spec.Ledger.BaseTypes (StrictMaybe)
import Shelley.Spec.Ledger.Coin (Coin)
import Shelley.Spec.Ledger.Scripts (ScriptHash)

--------------------------------------------------------------------------------
-- Era
--------------------------------------------------------------------------------

class
  ( CryptoClass.Crypto (Crypto e),
    Typeable e,
    WellFormed e
  ) =>
  Era e
  where
  type Crypto e :: Type

--------------------------------------------------------------------------------
-- Era translation
--------------------------------------------------------------------------------

-- | Map an era to its predecessor.
--
-- For example:
--
-- > type instance PreviousEra (AllegraEra c) = ShelleyEra c
type family PreviousEra era :: Type

-- | Per-era context used for 'TranslateEra'.
--
-- This context will be passed to the translation instances of /all/ types of
-- that particular era. In practice, most instances won't need the context, but
-- this approach makes the translation composable (as opposed to having a
-- separate context per type).
type family TranslationContext era :: Type

-- | Translation of types between eras, e.g., from Shelley to Allegra.
--
-- When @era@ is just a phantom type parameter, an empty standalone deriving can be used:
--
-- > newtype Foo era = Foo Int
-- >
-- > instance TranslateEra (Allegra c) Foo
--
-- Note that one could use @DerivingAnyClass@ (@deriving (TranslateEra (Allegra
-- c))@), but this would introduce an undesired coupling between the
-- era-parametric type and (a) particular era(s). The intention is to have a
-- module with orphan instances per era.
--
-- In most cases, the @era@ parameter won't be phantom, and a manual instance
-- will have to be written:
--
-- > newtype Bar era = Bar (TxBody era)
-- >
-- > instance CryptoClass.Crypto c => TranslateEra (Allegra c) Bar where
-- >     translateEra ctxt = Bar <$> translateEra ctxt
-- >
-- > -- With the following instance being in scope:
-- > instance CryptoClass.Crypto c => TranslatEra (Allegra c) TxBody
--
-- Note: we use 'PreviousEra' instead of @NextEra@ as an era definitely knows
-- its predecessor, but not necessarily its successor. Moreover, one could argue
-- that it makes more sense to define the translation from era A to era B where
-- era B is defined, than where era A is defined.
class (Era era, Era (PreviousEra era)) => TranslateEra era f where
  -- | Most translations should be infallible (default instance), but we leave
  -- the door open for partial translations.
  --
  -- For a partial translation, override the default type to be '()' or a
  -- concrete error type.
  type TranslationError era f :: Type

  type TranslationError era f = Void

  -- | Translate a type @f@ parameterised by the era from an era to the era
  -- after it.
  --
  -- The translation is a given the translation context of @era@.
  --
  -- A default instance is provided for when the two types are 'Coercible'.
  translateEra :: TranslationContext era -> f (PreviousEra era) -> Except (TranslationError era f) (f era)
  default translateEra ::
    Coercible (f (PreviousEra era)) (f era) =>
    TranslationContext era ->
    f (PreviousEra era) ->
    Except (TranslationError era f) (f era)
  translateEra _ = return . coerce

-- | Variant of 'translateEra' for when 'TranslationError' is 'Void' and the
-- translation thus cannot fail.
translateEra' ::
  (TranslateEra era f, TranslationError era f ~ Void) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  f era
translateEra' ctxt = either absurd id . runExcept . translateEra ctxt

-- | Variant of 'translateEra' for when 'TranslationError' is '()', converting
-- the result to a 'Maybe'.
translateEraMaybe ::
  (TranslateEra era f, TranslationError era f ~ ()) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  Maybe (f era)
translateEraMaybe ctxt =
  either (const Nothing) Just . runExcept . translateEra ctxt

-- ==========================================================
-- WellFormed-ness
-- ==========================================================

-- | All Well Formed Eras have this minimal structure.
type WellFormed era =
  ( -- TxBody
    HasField "outputs" (Core.TxBody era) (StrictSeq (Core.TxOut era)),
    HasField "txfee" (Core.TxBody era) Coin,
    HasField "minted" (Core.TxBody era) (Set (ScriptHash (Crypto era))),
    HasField "adHash" (Core.TxBody era) (StrictMaybe (AuxiliaryDataHash (Crypto era))),
    -- Tx
    HasField "body" (Core.Tx era) (Core.TxBody era),
    HasField "auxiliaryData" (Core.Tx era) (StrictMaybe (Core.AuxiliaryData era)),
    HasField "scriptWits" (Core.Tx era) (Map (ScriptHash (Crypto era)) (Core.Script era)),
    HasField "bootWits" (Core.Tx era) (Set (BootstrapWitness (Crypto era))),
    HasField "txsize" (Core.Tx era) Integer,
    -- TxOut
    HasField "address" (Core.TxOut era) (Addr (Crypto era)),
    HasField "value" (Core.TxOut era) (Core.Value era),
    -- HashAnnotated
    HashAnnotated (Core.AuxiliaryData era) EraIndependentAuxiliaryData (Crypto era),
    HashAnnotated (Core.TxBody era) EraIndependentTxBody (Crypto era),
    Val (Core.Value era),
    Compactible (Core.Value era) -- TxOut stores a CompactForm(Core.Value)
  )

{-  TODO, there are a few other constraints which are WellFormed and we should add
them when time permits. Some are not added because the types they mentions reside
in files that cause circular import dependencies.
   -- import Shelley.Spec.Ledger.TxBody(DCert,Wdrl,WitVKey)
   -- import Shelley.Spec.Ledger.Tx(TxIn)
These would have to be moved into a module such as Cardano.Ledger.TxBase(TxIn,DCert,Wdrl)
   -- HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),       -- all possible inputs
   -- HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era)))  -- inputs that can be used to pay fees
   -- HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
   -- HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
   -- HasField "addrWits" (Core.Tx era) (Set (WitVKey 'Witness (Crypto era)))
others where the concrete type (Update and WitnessSet) will have to be made into a type family
   -- import Shelley.Spec.Ledger.PParams (Update)
   -- import Shelley.Spec.Ledger.Tx(WitnessSet)
   -- import Cardano.Ledger.Alonzo.Scripts (ExUnits)
   -- HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
   -- HasField "witnessSet" (Core.Tx era) (WitnessSet era),
   -- HasField "exUnits" (Core.Tx era) ExUnits,
-}
