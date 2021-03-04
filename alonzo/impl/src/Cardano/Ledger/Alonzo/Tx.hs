{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module exports implementations of many of the functions outlined in the Alonzo specification.
--     The link to source of the specification
--       https://github.com/input-output-hk/cardano-ledger-specs/tree/master/alonzo/formal-spec
--     The most recent version of the document can be found here:
--       https://hydra.iohk.io/job/Cardano/cardano-ledger-specs/specs.alonzo-ledger/latest/download-by-type/doc-pdf/alonzo-changes
--     The functions can be found in Figures in that document, and sections of this code refer to those figures.
module Cardano.Ledger.Alonzo.Tx
  ( Indexable (..),
    -- Figure 1
    CostModel,
    getLanguageView,
    -- Figure 2
    Data,
    DataHash,
    IsValidating (..),
    hashData,
    language,
    nonNativeLanguages,
    hashWitnessPPData,
    getCoin,
    EraIndependentWitnessPPData,
    WitnessPPData,
    WitnessPPDataHash,
    -- Figure 3
    Tx (Tx, body, wits, isValidating, auxiliaryData),
    body',
    wits',
    isValidating',
    auxiliaryData',
    TxBody (..),
    -- Figure 4
    ScriptPurpose (..),
    --  Figure 5
    getValidatorHash,
    txbody,
    minfee,
    isNonNativeScriptAddress,
    txins,
    Shelley.txouts,
    -- Figure 6
    txrdmrs,
    rdptr,
    getMapFromValue,
    indexedRdmrs,
    -- Figure 7
    valContext,
    runPLCScript,
    -- Figure 8
    getData,
    collectNNScriptInputs,
    evalScripts,
    -- Figure 12
    scriptsNeeded,
    checkScriptData,
    -- Pretty
    ppIsValidating,
    ppTx,
  )
where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.Alonzo.Data (Data, DataHash, hashData)
import Cardano.Ledger.Alonzo.Language (Language (..), nonNativeLanguages)
import Cardano.Ledger.Alonzo.PParams (LangDepView (..), PParams, getLanguageView)
import Cardano.Ledger.Alonzo.Scripts (CostModel, ExUnits (..), Prices, scriptfee)
import qualified Cardano.Ledger.Alonzo.Scripts as AlonzoScript (Script (..), Tag (..))
import Cardano.Ledger.Alonzo.TxBody
  ( EraIndependentWitnessPPData,
    TxBody (..),
    TxOut (..),
    WitnessPPDataHash,
  )
import Cardano.Ledger.Alonzo.TxWitness
  ( RdmrPtr (..),
    TxWitness (..),
    ppTxWitness,
    txdats,
    txrdmrs,
    txscripts,
  )
import Cardano.Ledger.Compactible
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Mary.Value (AssetName, PolicyID (..), Value (..))
import Cardano.Ledger.Pretty
  ( PDoc,
    PrettyA (..),
    ppRecord,
    ppStrictMaybe,
    ppString,
  )
import Cardano.Ledger.SafeHash
  ( HashAnnotated,
    SafeToHash,
    hashAnnotated,
  )
import Cardano.Ledger.Shelley.Constraints
import Cardano.Ledger.Val (DecodeMint, DecodeNonNegative, Val (coin, (<+>), (<×>)))
import qualified Data.ByteString.Short as SBS (length)
import Data.Coders
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (isJust, maybeToList)
import Data.MemoBytes (Mem, MemoBytes (Memo), memoBytes)
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
  ( elemAt,
    findIndex,
    map,
    null,
    union,
  )
import Data.Typeable (Typeable)
import Data.Word (Word64)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.Address (Addr (..), RewardAcnt, getRwdCred)
import Shelley.Spec.Ledger.Address.Bootstrap (BootstrapWitness)
import Shelley.Spec.Ledger.BaseTypes (StrictMaybe, maybeToStrictMaybe, strictMaybeToMaybe)
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Credential (Credential (ScriptHashObj))
import Shelley.Spec.Ledger.Delegation.Certificates (DCert (..))
import Shelley.Spec.Ledger.Keys (KeyRole (Witness))
import Shelley.Spec.Ledger.Scripts (ScriptHash)
import Shelley.Spec.Ledger.Tx (ValidateScript (isNativeScript))
import Shelley.Spec.Ledger.TxBody (DelegCert (..), Delegation (..), TxIn (..), Wdrl (..), WitVKey, unWdrl)
import Shelley.Spec.Ledger.UTxO (UTxO (..))
import qualified Shelley.Spec.Ledger.UTxO as Shelley

-- ===================================================

-- | Tag indicating whether non-native scripts in this transaction are expected
-- to validate. This is added by the block creator when constructing the block.
newtype IsValidating = IsValidating Bool
  deriving (Eq, Show, Generic)
  deriving newtype (NoThunks)

data TxRaw era = TxRaw
  { _body :: !(Core.TxBody era),
    _wits :: !(TxWitness era),
    _isValidating :: !IsValidating,
    _auxiliaryData :: !(StrictMaybe (Core.AuxiliaryData era))
  }
  deriving (Generic, Typeable)

deriving instance
  ( Era era,
    Eq (Core.AuxiliaryData era),
    Eq (Core.Script era),
    Eq (Core.TxBody era),
    Eq (Core.Value era),
    Eq (PParamsDelta era),
    Compactible (Core.Value era)
  ) =>
  Eq (TxRaw era)

deriving instance
  ( Era era,
    Compactible (Core.Value era),
    Show (Core.AuxiliaryData era),
    Show (Core.Script era),
    Show (Core.TxBody era),
    Show (Core.Value era),
    Show (PParamsDelta era)
  ) =>
  Show (TxRaw era)

instance
  ( Era era,
    NoThunks (Core.AuxiliaryData era),
    NoThunks (Core.Script era),
    NoThunks (Core.TxBody era),
    NoThunks (Core.Value era),
    NoThunks (PParamsDelta era)
  ) =>
  NoThunks (TxRaw era)

newtype Tx era = TxConstr (MemoBytes (TxRaw era))
  deriving newtype (ToCBOR)

deriving newtype instance
  ( Era era,
    Eq (Core.AuxiliaryData era),
    Eq (Core.Script era),
    Eq (Core.TxBody era),
    Eq (Core.Value era),
    Eq (PParamsDelta era),
    Compactible (Core.Value era)
  ) =>
  Eq (Tx era)

deriving newtype instance
  ( Era era,
    Compactible (Core.Value era),
    Show (Core.AuxiliaryData era),
    Show (Core.Script era),
    Show (Core.TxBody era),
    Show (Core.Value era),
    Show (PParamsDelta era)
  ) =>
  Show (Tx era)

deriving newtype instance
  ( Era era,
    NoThunks (Core.AuxiliaryData era),
    NoThunks (Core.Script era),
    NoThunks (Core.TxBody era),
    NoThunks (Core.Value era),
    NoThunks (PParamsDelta era)
  ) =>
  NoThunks (Tx era)

pattern Tx ::
  ( Era era,
    ToCBOR (Core.AuxiliaryData era),
    ToCBOR (Core.TxBody era)
  ) =>
  Core.TxBody era ->
  TxWitness era ->
  IsValidating ->
  StrictMaybe (Core.AuxiliaryData era) ->
  Tx era
pattern Tx {body, wits, isValidating, auxiliaryData} <-
  TxConstr
    ( Memo
        TxRaw
          { _body = body,
            _wits = wits,
            _isValidating = isValidating,
            _auxiliaryData = auxiliaryData
          }
        _
      )
  where
    Tx b w v a = TxConstr $ memoBytes (encodeTxRaw $ TxRaw b w v a)

-- We define these accessor functions manually, because if we define them using
-- the record syntax in the Tx pattern, they inherit the constraints
-- (Era era, ToCBOR (Core.AuxiliaryData era),ToCBOR (Core.TxBody era))
-- constraint as a precondition. This is unnecessary, as one can see below.

body' :: Tx era -> Core.TxBody era
body' (TxConstr (Memo (TxRaw b _ _ _) _)) = b

wits' :: Tx era -> TxWitness era
wits' (TxConstr (Memo (TxRaw _ x _ _) _)) = x

isValidating' :: Tx era -> IsValidating
isValidating' (TxConstr (Memo (TxRaw _ _ x _) _)) = x

auxiliaryData' :: Tx era -> StrictMaybe (Core.AuxiliaryData era)
auxiliaryData' (TxConstr (Memo (TxRaw _ _ _ x) _)) = x

-- ===================================
-- WellFormed instances

instance aux ~ (Core.AuxiliaryData era) => HasField "auxiliaryData" (Tx era) (StrictMaybe aux) where
  getField txr = auxiliaryData' txr

instance (body ~ Core.TxBody era) => HasField "body" (Tx era) body where
  getField txr = body' txr

instance HasField "wits" (Tx era) (TxWitness era) where
  getField txr = wits' txr

instance HasField "isValidating" (Tx era) IsValidating where
  getField txr = isValidating' txr

instance c ~ (Crypto era) => HasField "addrWits" (Tx era) (Set (WitVKey 'Witness c)) where
  getField (TxConstr (Memo (TxRaw _ x _ _) _)) = txwitsVKey' x

instance
  (c ~ (Crypto era), script ~ Core.Script era) =>
  HasField "scriptWits" (Tx era) (Map.Map (ScriptHash c) script)
  where
  getField (TxConstr (Memo (TxRaw _ x _ _) _)) = txscripts' x

instance c ~ (Crypto era) => HasField "bootWits" (Tx era) (Set (BootstrapWitness c)) where
  getField (TxConstr (Memo (TxRaw _ x _ _) _)) = txwitsBoot' x

-- =========================================================
-- Figure 2: Definitions for Transactions

getCoin :: UsesValue era => TxOut era -> Coin
getCoin (TxOut _ v _) = coin v

-- ========================================================================
-- A WitnessPPDataHash is the hash of two things. The first part comes from
-- the witnesses and the second comes from the Protocol Parameters (PParams).
-- In order to hash 2 things we make a newtype WitnessPPData which will be
-- a MemoBytes of these two things (WitnessPPDataRaw), so that we can hash it.

data WitnessPPDataRaw era
  = WitnessPPDataRaw
      !(Map.Map RdmrPtr (Data era)) -- From the witnesses
      !(Set (LangDepView era)) -- From the Porotocl parameters
  deriving (Show, Eq, Generic, Typeable)

deriving instance NoThunks (WitnessPPDataRaw era)

instance Era era => ToCBOR (WitnessPPDataRaw era) where
  toCBOR (WitnessPPDataRaw m s) = encode (Rec WitnessPPDataRaw !> To m !> To s)

instance Era era => FromCBOR (Annotator (WitnessPPDataRaw era)) where
  fromCBOR =
    decode
      ( Ann (RecD WitnessPPDataRaw)
          <*! mapDecodeA (Ann From) From
          <*! setDecodeA From
      )

newtype WitnessPPData era = WitnessPPDataConstr (MemoBytes (WitnessPPDataRaw era))
  deriving (Show, Eq)
  deriving newtype (ToCBOR, SafeToHash)

deriving via
  (Mem (WitnessPPDataRaw era))
  instance
    Era era => FromCBOR (Annotator (WitnessPPData era))

pattern WitnessPPData ::
  Era era =>
  Map.Map RdmrPtr (Data era) ->
  Set (LangDepView era) ->
  WitnessPPData era
pattern WitnessPPData mp s <-
  WitnessPPDataConstr (Memo (WitnessPPDataRaw mp s) _)
  where
    WitnessPPData mp s =
      WitnessPPDataConstr
        . memoBytes
        $ (Rec WitnessPPDataRaw !> mapEncode mp !> setEncode s)

instance (c ~ Crypto era) => HashAnnotated (WitnessPPData era) EraIndependentWitnessPPData c

hashWitnessPPData ::
  forall era.
  Era era =>
  PParams era ->
  Set Language ->
  Map.Map RdmrPtr (Data era) ->
  Maybe (WitnessPPDataHash (Crypto era))
hashWitnessPPData pp langs rdmrs =
  if Map.null rdmrs && Set.null langs
    then Nothing
    else
      let newset = Set.map (getLanguageView pp) langs
       in Just (hashAnnotated (WitnessPPData rdmrs newset))

-- ===============================================================
-- From the specification, Figure 5 "Functions related to fees"
-- ===============================================================

isNonNativeScriptAddress ::
  forall era.
  (Era era, ValidateScript era) =>
  Core.Tx era ->
  Addr (Crypto era) ->
  Bool
isNonNativeScriptAddress tx addr =
  case getValidatorHash addr of
    Nothing -> False
    Just hash ->
      case Map.lookup hash (getField @"scriptWits" tx) of
        Nothing -> False
        Just scr -> not (isNativeScript @era scr)

-- | The keys of all the inputs of the TxBody (both the inputs for fees, and the normal inputs).
txins ::
  ( HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era)))
  ) =>
  Core.TxBody era ->
  Set (TxIn (Crypto era))
txins txb = Set.union (getField @"inputs" txb) (getField @"txinputs_fee" txb)

-- | txsize computes the length of the serialised bytes
instance HasField "txsize" (Tx era) Integer where
  getField (TxConstr (Memo _ bytes)) = fromIntegral (SBS.length bytes)

minfee ::
  ( HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices,
    HasField "totExunits" (Core.Tx era) ExUnits,
    HasField "txsize" (Core.Tx era) Integer
  ) =>
  Core.PParams era ->
  Core.Tx era ->
  Coin
minfee pp tx =
  (getField @"txsize" tx <×> a pp)
    <+> b pp
    <+> (scriptfee (getField @"_prices" pp) allExunits)
  where
    a protparam = Coin (fromIntegral (getField @"_minfeeA" protparam))
    b protparam = Coin (fromIntegral (getField @"_minfeeB" protparam))
    allExunits = getField @"totExunits" tx

-- The only thing that keeps minfee from working on Core.Tx is that
-- not all eras can extract a ExUninits from a Core.Tx. For the Alonzo
-- era, we use this function, specialized to the Alonzo Tx defined in this file.
-- If we had instances (HasField "exUnits" (Core.Tx era) ExUnits) we'd be golden

instance HasField "totExunits" (Tx era) ExUnits where
  getField tx = foldl (<>) mempty (snd $ unzip (Map.elems trd))
    where
      trd = getField @"txrdmrs" (getField @"wits" tx)

-- The specification uses "validatorHash" to extract ScriptHash from
-- an Addr. But not every Addr has a ScriptHash. In particular KeyHashObj
-- do not. So we use getValidatorHash which returns a Maybe type.

getValidatorHash :: Addr crypto -> Maybe (ScriptHash crypto)
getValidatorHash (Addr _network (ScriptHashObj hash) _ref) = Just hash
getValidatorHash _ = Nothing

txbody :: Tx era -> Core.TxBody era
txbody (TxConstr (Memo TxRaw {_body = b} _)) = b

-- ===============================================================
-- Operations on scripts from specification
-- Figure 6:Indexing script and data objects
-- ===============================================================

data ScriptPurpose crypto
  = Minting !(PolicyID crypto)
  | Spending !(TxIn crypto)
  | Rewarding !(RewardAcnt crypto) -- Not sure if this is the right type.
  | Certifying !(DCert crypto)
  deriving (Eq)

class Indexable elem container where
  indexOf :: elem -> container -> Word64
  atIndex :: Word64 -> container -> elem

instance Ord k => Indexable k (Set k) where
  indexOf n set = fromIntegral $ Set.findIndex n set
  atIndex i set = Set.elemAt (fromIntegral i) set

instance Eq k => Indexable k (StrictSeq k) where
  indexOf n seqx = case StrictSeq.findIndexL (== n) seqx of
    Just m -> fromIntegral m
    Nothing -> error "Not found in StrictSeq"
  atIndex i seqx = case StrictSeq.lookup (fromIntegral i) seqx of
    Just element -> element
    Nothing -> error ("No elem at index " ++ show i)

instance Ord k => Indexable k (Map.Map k v) where
  indexOf n mp = fromIntegral $ Map.findIndex n mp
  atIndex i mp = fst (Map.elemAt (fromIntegral i) mp) -- If one needs the value, on can use Map.Lookup

rdptr ::
  forall era.
  ( HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "mint" (Core.TxBody era) (Value (Crypto era))
  ) =>
  Core.TxBody era ->
  ScriptPurpose (Crypto era) ->
  RdmrPtr
rdptr txb (Minting pid) = RdmrPtr AlonzoScript.Mint (indexOf pid (getMapFromValue (getField @"mint" txb)))
rdptr txb (Spending txin) = RdmrPtr AlonzoScript.Spend (indexOf txin (getField @"inputs" txb))
rdptr txb (Rewarding racnt) = RdmrPtr AlonzoScript.Rewrd (indexOf racnt (unWdrl (getField @"wdrls" txb)))
rdptr txb (Certifying d) = RdmrPtr AlonzoScript.Cert (indexOf d (getField @"certs" txb))

getMapFromValue :: Value crypto -> Map.Map (PolicyID crypto) (Map.Map AssetName Integer)
getMapFromValue (Value _ m) = m

indexedRdmrs ::
  forall era.
  ( Era era,
    ToCBOR (Core.Script era),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "mint" (Core.TxBody era) (Value (Crypto era))
  ) =>
  Tx era ->
  ScriptPurpose (Crypto era) ->
  Maybe (Data era, ExUnits)
indexedRdmrs tx sp = Map.lookup policyid (txrdmrs . getField @"wits" $ tx)
  where
    policyid = rdptr @era (getField @"body" tx) sp

-- ===============================================================
-- From the specification, Figure 7 "Script Validation, cont."
-- ===============================================================

-- | valContext collects info from the Tx and the UTxO and translates it into
--   a 'Data', which the Plutus language knows how to interpret.
valContext :: UTxO era -> Tx era -> ScriptPurpose (Crypto era) -> [Data era]
valContext _utxo _tx _sp = []

--TODO FIX THIS, when defined will always return singleton list
-- see also: collectNNScriptInputs    where it is called

-- TODO  Specification says CostMod, not CostModel
runPLCScript ::
  CostModel ->
  AlonzoScript.Script era ->
  [Data era] ->
  ExUnits ->
  (IsValidating, ExUnits)
runPLCScript _cost _script _data _exunits = (IsValidating True, ExUnits 0 0) -- TODO FIX THIS

-- ===============================================================
-- From the specification, Figure 8 "Scripts and their Arguments"
-- ===============================================================

getData ::
  forall era.
  ( ToCBOR (Core.Script era),
    UsesTxOut era,
    HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era)))
  ) =>
  Tx era ->
  UTxO era ->
  ScriptPurpose (Crypto era) ->
  [Data era]
getData tx (UTxO m) sp = case sp of
  Minting _policyid -> []
  Rewarding _rewaccnt -> []
  Certifying _dcert -> []
  Spending txin ->
    -- Only the Spending ScriptPurpose contains Data
    case Map.lookup txin m of
      Nothing -> []
      Just txout ->
        case getField @"datahash" txout of
          Nothing -> []
          Just hash ->
            case Map.lookup hash (txdats (getField @"wits" tx)) of
              Nothing -> []
              Just d -> [d]

collectNNScriptInputs ::
  ( UsesTxOut era,
    ToCBOR (Core.Script era),
    Core.Script era ~ AlonzoScript.Script era,
    HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era))),
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "mint" (Core.TxBody era) (Value (Crypto era)),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era)))
  ) =>
  Core.PParams era ->
  Tx era ->
  UTxO era ->
  [(AlonzoScript.Script era, [Data era], ExUnits, CostModel)]
collectNNScriptInputs pp tx utxo =
  [ (script, d : (valContext utxo tx sp ++ getData tx utxo sp), eu, cost)
    | (sp, scripthash) <- scriptsNeeded utxo tx, -- TODO, IN specification ORDER IS WRONG
      (d, eu) <- maybeToList (indexedRdmrs tx sp),
      script <- maybeToList (Map.lookup scripthash (txscripts (getField @"wits" tx))),
      cost <- case language script of
        Nothing -> []
        Just lang -> maybeToList (Map.lookup lang (getField @"_costmdls" pp))
  ]

language :: AlonzoScript.Script era -> Maybe Language
language (AlonzoScript.NativeScript _) = Nothing
language AlonzoScript.PlutusScript = Just PlutusV1

evalScripts ::
  [(AlonzoScript.Script era, [Data era], ExUnits, CostModel)] ->
  Bool
evalScripts [] = True
evalScripts ((AlonzoScript.NativeScript _timelock, _, _, _) : rest) =
  evalScripts rest
evalScripts ((AlonzoScript.PlutusScript, ds, units, cost) : rest) =
  b && evalScripts rest
  where
    (IsValidating b, _exunits) = runPLCScript cost AlonzoScript.PlutusScript ds units

-- ===================================================================
-- From Specification, Figure 12 "UTXOW helper functions"

-- THE SPEC CALLS FOR A SET, BUT THAT NEEDS A BUNCH OF ORD INSTANCES (DCert)
scriptsNeeded ::
  forall era.
  ( UsesTxOut era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "mint" (Core.TxBody era) (Value (Crypto era))
  ) =>
  UTxO era ->
  Tx era ->
  [(ScriptPurpose (Crypto era), ScriptHash (Crypto era))]
scriptsNeeded (UTxO utxomap) tx = spend ++ reward ++ cert ++ minted
  where
    txb = txbody tx
    !spend = foldl' accum [] (getField @"inputs" txb)
      where
        accum !ans !i =
          case Map.lookup i utxomap of
            Nothing -> ans
            Just txout ->
              case getValidatorHash (getField @"address" txout) of
                Nothing -> ans
                Just hash -> (Spending i, hash) : ans

    !reward = foldl' accum [] (Map.keys m2)
      where
        (Wdrl m2) = getField @"wdrls" txb
        accum !ans !accnt = case getRwdCred accnt of -- TODO  IS THIS RIGHT?
          (ScriptHashObj hash) -> (Rewarding accnt, hash) : ans
          _ -> ans

    !cert = foldl addOnlyCwitness [] (getField @"certs" txb)

    !minted = map (\pid@(PolicyID hash) -> (Minting pid, hash)) (Map.keys m3)
      where
        m3 = getMapFromValue (getField @"mint" txb)

-- We only find certificate witnesses in Delegating and Deregistration DCerts
-- that have ScriptHashObj credentials.
addOnlyCwitness ::
  [(ScriptPurpose crypto, ScriptHash crypto)] ->
  DCert crypto ->
  [(ScriptPurpose crypto, ScriptHash crypto)]
addOnlyCwitness !ans (DCertDeleg c@(DeRegKey (ScriptHashObj hk))) =
  (Certifying $ DCertDeleg c, hk) : ans
addOnlyCwitness !ans (DCertDeleg c@(Delegate (Delegation (ScriptHashObj hk) _dpool))) =
  (Certifying $ DCertDeleg c, hk) : ans
addOnlyCwitness !ans _ = ans

checkScriptData ::
  forall era.
  ( ValidateScript era,
    UsesTxOut era,
    HasField "datahash" (Core.TxOut era) (Maybe (DataHash (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "mint" (Core.TxBody era) (Value (Crypto era))
  ) =>
  Tx era ->
  UTxO era ->
  (ScriptPurpose (Crypto era), ScriptHash (Crypto era)) ->
  Bool
checkScriptData tx utxo (sp, _h) = any ok scripts
  where
    scripts = txscripts (getField @"wits" tx)
    isSpending (Spending _) = True
    isSpending _ = False
    ok s =
      isNativeScript @era s
        || ( isJust (indexedRdmrs tx sp)
               && (not (isSpending sp) || not (null (getData tx utxo sp)))
           )

-- =======================================================

ppIsValidating :: IsValidating -> PDoc
ppIsValidating (IsValidating True) = ppString "True"
ppIsValidating (IsValidating False) = ppString "False"

instance PrettyA IsValidating where prettyA = ppIsValidating

ppTx ::
  ( Era era,
    PrettyA (Core.Script era),
    PrettyA (Core.TxBody era),
    PrettyA (Core.AuxiliaryData era)
  ) =>
  Tx era ->
  PDoc
ppTx (TxConstr (Memo (TxRaw b w iv aux) _)) =
  ppRecord
    "Tx"
    [ ("body", prettyA b),
      ("wits", ppTxWitness w),
      ("isValidating", ppIsValidating iv),
      ("auxiliaryData", ppStrictMaybe prettyA aux)
    ]

instance
  ( Era era,
    PrettyA (Core.Script era),
    PrettyA (Core.TxBody era),
    PrettyA (Core.AuxiliaryData era)
  ) =>
  PrettyA (Tx era)
  where
  prettyA = ppTx

--------------------------------------------------------------------------------
-- Serialisation
--------------------------------------------------------------------------------

deriving newtype instance FromCBOR IsValidating

deriving newtype instance ToCBOR IsValidating

encodeTxRaw ::
  ( Era era,
    ToCBOR (Core.AuxiliaryData era),
    ToCBOR (Core.TxBody era)
  ) =>
  TxRaw era ->
  Encode ('Closed 'Dense) (TxRaw era)
encodeTxRaw TxRaw {_body, _wits, _isValidating, _auxiliaryData} =
  Rec TxRaw
    !> To _body
    !> To _wits
    !> To _isValidating
    !> E (encodeNullMaybe toCBOR . strictMaybeToMaybe) _auxiliaryData

instance
  ( Era era,
    FromCBOR (Annotator (Core.Script era)),
    FromCBOR (Annotator (Core.TxBody era)),
    FromCBOR (Annotator (Core.AuxiliaryData era)),
    Core.AnnotatedData (PParamsDelta era),
    ToCBOR (Core.Script era),
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era),
    Compactible (Core.Value era),
    DecodeNonNegative (Core.Value era),
    DecodeMint (Core.Value era),
    Show (Core.Value era),
    Val (Core.Value era)
  ) =>
  FromCBOR (Annotator (TxRaw era))
  where
  fromCBOR =
    decode $
      Ann (RecD TxRaw)
        <*! From
        <*! From
        <*! Ann From
        <*! D
          ( sequence . maybeToStrictMaybe
              <$> decodeNullMaybe fromCBOR
          )

deriving via
  Mem (TxRaw era)
  instance
    ( Era era,
      FromCBOR (Annotator (Core.Script era)),
      FromCBOR (Annotator (Core.TxBody era)),
      FromCBOR (Annotator (Core.AuxiliaryData era)),
      Core.AnnotatedData (PParamsDelta era),
      ToCBOR (Core.Script era),
      Typeable (Core.Script era),
      Typeable (Core.AuxiliaryData era),
      Compactible (Core.Value era),
      DecodeNonNegative (Core.Value era),
      DecodeMint (Core.Value era),
      Show (Core.Value era),
      Val (Core.Value era)
    ) =>
    FromCBOR (Annotator (Tx era))
