{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- The STS instance for UTXOW is technically an orphan.
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.ShelleyMA.Rules.Utxow where

import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.ShelleyMA.Rules.Utxo (UTXO, UtxoPredicateFailure)
import Cardano.Ledger.ShelleyMA.TxBody ()
import Control.State.Transition.Extended
import Shelley.Spec.Ledger.BaseTypes
import Shelley.Spec.Ledger.LedgerState (UTxOState)
import qualified Shelley.Spec.Ledger.STS.Ledger as Shelley
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv)
import Shelley.Spec.Ledger.STS.Utxow
  ( ShelleyStyleWitnessNeeds,
    UtxowPredicateFailure (..),
    shelleyStyleWitness,
  )
import Shelley.Spec.Ledger.Tx (Tx)

-- ==============================================================================
--   We want to reuse the same rules for Mary and Allegra. We accomplish this
--   by adding: HasField "minted" (Core.TxBody era) (Set (ScriptHash (Crypto era)))
--   to the (WellFormed era) constraint, and adjusting UTxO.(ScriptsNeeded) to
--   add this set to its output. In the Shelley and Allegra Era, this is the empty set.
--   With this generalization, Shelley.Spec.Ledger.STS.Utxow(shelleyStyleWitness)
--   can still be used in Allegra and Mary, because they use the same Shelley style rules.

--------------------------------------------------------------------------------
-- UTXOW STS
--------------------------------------------------------------------------------

data UTXOW era

instance
  forall era.
  ( -- Fix Core.Tx to the Allegra and Mary Era
    Core.Tx era ~ Tx era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (UTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ Tx era,
    -- Supply the HasField and Validate instances for Mary and Allegra (which match Shelley)
    ShelleyStyleWitnessNeeds era
  ) =>
  STS (UTXOW era)
  where
  type State (UTXOW era) = UTxOState era
  type Signal (UTXOW era) = Tx era
  type Environment (UTXOW era) = UtxoEnv era
  type BaseM (UTXOW era) = ShelleyBase
  type
    PredicateFailure (UTXOW era) =
      UtxowPredicateFailure era
  transitionRules = [shelleyStyleWitness]
  initialRules = []

instance
  ( Era era,
    STS (UTXO era),
    PredicateFailure (Core.EraRule "UTXO" era) ~ UtxoPredicateFailure era
  ) =>
  Embed (UTXO era) (UTXOW era)
  where
  wrapFailed = UtxoFailure

instance
  ( Era era,
    STS (UTXOW era),
    PredicateFailure (Core.EraRule "UTXOW" era) ~ UtxowPredicateFailure era
  ) =>
  Embed (UTXOW era) (Shelley.LEDGER era)
  where
  wrapFailed = Shelley.UtxowFailure
