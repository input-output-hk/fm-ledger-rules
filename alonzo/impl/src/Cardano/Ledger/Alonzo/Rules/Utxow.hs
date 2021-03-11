{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo.Rules.Utxow where

-- import Shelley.Spec.Ledger.UTxO(UTxO(..))

import Cardano.Ledger.Alonzo.Data (Data, DataHash)
import Cardano.Ledger.Alonzo.PParams (PParams)
import Cardano.Ledger.Alonzo.Rules.Utxo (AlonzoUTXO)
import qualified Cardano.Ledger.Alonzo.Rules.Utxo as Alonzo (UtxoPredicateFailure)
import Cardano.Ledger.Alonzo.Scripts (Script)
import Cardano.Ledger.Alonzo.Tx
  ( ScriptPurpose,
    Tx,
    checkScriptData,
    hashWitnessPPData,
    isNonNativeScriptAddress,
    language,
    scriptsNeeded,
    wits',
  )
import Cardano.Ledger.Alonzo.TxBody (WitnessPPDataHash)
import Cardano.Ledger.Alonzo.TxWitness (TxWitness (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.SafeHash (EraIndependentData, SafeHash)
import Control.Iterate.SetAlgebra (domain, eval, (◁))
import Control.State.Transition.Extended
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Records
import Shelley.Spec.Ledger.BaseTypes
  ( ShelleyBase,
    StrictMaybe (..),
  )
import Shelley.Spec.Ledger.LedgerState (UTxOState (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.STS.Utxow
  ( ShelleyStyleWitnessNeeds,
    UtxowPredicateFailure (..),
    shelleyStyleWitness,
  )
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.Tx (TxIn (..), ValidateScript (..))

-- =====================================================

{- Defined in the Shelley Utxow rule.
type ShelleyStyleWitnessNeeds era =
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "addrWits" (Core.Tx era) (Set (WitVKey 'Witness (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    ValidateAuxiliaryData era (Crypto era),
    ValidateScript era,
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
  )
-}

type AlonzoStyleAdditions era =
  ( HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era))), -- BE SURE AND ADD THESE INSTANCES
    HasField "txdatahash" (Core.Tx era) (Map.Map (DataHash (Crypto era)) (Data era)),
    HasField "sdHash" (Core.TxBody era) (StrictMaybe (WitnessPPDataHash (Crypto era)))
  )

alonzoStyleWitness ::
  forall era utxow.
  ( Era era,
    -- Fix some Core types to the Alonzo Era
    Core.Tx era ~ Tx era, -- scriptsNeeded, checkScriptData etc. are fixed at Alonzo.Tx
    Core.PParams era ~ PParams era,
    Core.Script era ~ Script era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (utxow era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ Core.Tx era,
    -- Asumptions needed since we are going to fix utxow when we use this in an STS Era
    BaseM (utxow era) ~ ShelleyBase,
    Environment (utxow era) ~ UtxoEnv era,
    State (utxow era) ~ UTxOState era,
    Signal (utxow era) ~ Core.Tx era,
    PredicateFailure (utxow era) ~ UtxowPredicateFailure era,
    STS (utxow era),
    -- Supply the HasField and Validate instances for Alonzo
    ShelleyStyleWitnessNeeds era,
    AlonzoStyleAdditions era
  ) =>
  TransitionRule (utxow era)
alonzoStyleWitness = do
  _u <- shelleyStyleWitness
  (TRC (UtxoEnv _slot pp _stakepools _genDelegs, u', tx)) <- judgmentContext
  let txbody = getField @"body" (tx :: Core.Tx era)

  let scriptWitMap = getField @"scriptWits" tx
      failedScripts = Map.foldr accum [] scriptWitMap
        where
          accum script bad = if validateScript @era script tx then bad else script : bad
  null failedScripts ?! error ("Scripts don't validate")

  let utxo = _utxo u'
      sphs :: [(ScriptPurpose (Crypto era), ScriptHash (Crypto era))]
      sphs = scriptsNeeded utxo tx
      unredeemed = filter (checkScriptData tx utxo) sphs
  null unredeemed ?! error ("some scripts aren't redeemed")

  let txScriptSet = Map.keysSet scriptWitMap
      needed = Set.fromList [script | (_purpose, script) <- sphs]
  needed == txScriptSet ?! error ("some scripts not accounted for")

  let inputs = getField @"inputs" txbody :: (Set (TxIn (Crypto era)))
      smallUtxo = eval (inputs ◁ utxo) :: Map.Map (TxIn (Crypto era)) (Core.TxOut era)
      utxoHashes :: [SafeHash (Crypto era) EraIndependentData]
      utxoHashes =
        [ h
          | (_input, output) <- Map.toList smallUtxo,
            Just h <- [getField @"datahash" output],
            isNonNativeScriptAddress @era tx (getField @"address" output)
        ]
      txHashes = domain (getField @"txdatahash" tx)
  txHashes == Set.fromList utxoHashes ?! error ("something bad")

  let languages =
        [ l
          | (_hash, script) <- Map.toList scriptWitMap,
            isNativeScript @era script,
            Just l <- [language @era script]
        ]
      rdmrs wit = Map.map fst (txrdmrs wit)
      computedPPhash = hashWitnessPPData pp (Set.fromList languages) (rdmrs (wits' tx))
      bodyPPhash = getField @"sdHash" txbody
  bodyPPhash == computedPPhash ?! error ("Another bad thing")
  pure u'

-- ====================================
-- Make the STS instance

data AlonzoUTXOW era

instance
  forall era.
  ( -- Fix some Core types to the Alonzo Era
    Core.Tx era ~ Tx era,
    Core.PParams era ~ PParams era,
    Core.Script era ~ Script era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (AlonzoUTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ Tx era,
    -- Supply the HasField and Validate instances for Alonzo
    ShelleyStyleWitnessNeeds era, -- supplies a subset of those needed. All the old Shelley Needs still apply.
    AlonzoStyleAdditions era
  ) =>
  STS (AlonzoUTXOW era)
  where
  type State (AlonzoUTXOW era) = UTxOState era
  type Signal (AlonzoUTXOW era) = Tx era
  type Environment (AlonzoUTXOW era) = UtxoEnv era
  type BaseM (AlonzoUTXOW era) = ShelleyBase
  type
    PredicateFailure (AlonzoUTXOW era) =
      UtxowPredicateFailure era
  transitionRules = [alonzoStyleWitness]
  initialRules = []

instance
  ( Era era,
    STS (AlonzoUTXO era),
    PredicateFailure (Core.EraRule "UTXO" era) ~ Alonzo.UtxoPredicateFailure era,
    BaseM (AlonzoUTXOW era) ~ ShelleyBase,
    PredicateFailure (AlonzoUTXOW era) ~ UtxowPredicateFailure era
  ) =>
  Embed (AlonzoUTXO era) (AlonzoUTXOW era)
  where
  wrapFailed = UtxoFailure
