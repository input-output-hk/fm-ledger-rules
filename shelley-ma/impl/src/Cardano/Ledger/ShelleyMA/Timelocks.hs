{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.ShelleyMA.Timelocks
  ( Timelock (RequireSignature, RequireAllOf, RequireAnyOf, RequireMOf, RequireTimeExpire, RequireTimeStart),
    pattern TimelockConstr,
    inInterval,
    showTimelock,
    validateTimelock,
    ValidityInterval (..),
    encodeVI,
    decodeVI,
    translate,
    ppTimelock,
    ppValidityInterval,
  )
where

import Cardano.Binary
  ( Annotator (..),
    FromCBOR (fromCBOR),
    FullByteString (Full),
    ToCBOR (toCBOR),
  )
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era
import Cardano.Ledger.Pretty
  ( PDoc,
    PrettyA (..),
    ppInteger,
    ppKeyHash,
    ppRecord,
    ppSexp,
    ppSlotNo,
    ppStrictMaybe,
  )
import Cardano.Ledger.SafeHash (SafeToHash)
import Cardano.Ledger.Shelley.Constraints (UsesScript, UsesTxBody)
import Cardano.Slotting.Slot (SlotNo (..))
import Codec.CBOR.Read (deserialiseFromBytes)
import Control.DeepSeq (NFData (..))
import qualified Data.ByteString.Lazy as Lazy
import Data.ByteString.Short (fromShort)
import Data.Coders
  ( Decode (..),
    Density (..),
    Encode (..),
    Wrapped (..),
    decode,
    encode,
    (!>),
    (<!),
    (<*!),
  )
import Data.MemoBytes
  ( Mem,
    MemoBytes (..),
    memoBytes,
  )
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set, member)
import qualified Data.Set as Set
import Data.Typeable
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.BaseTypes (StrictMaybe (SJust, SNothing))
import Shelley.Spec.Ledger.Keys (KeyHash (..), KeyRole (Witness))
import Shelley.Spec.Ledger.Scripts (MultiSig, getMultiSigBytes)
import Shelley.Spec.Ledger.Serialization
  ( decodeStrictSeq,
    encodeFoldable,
  )
import Shelley.Spec.Ledger.Tx
  ( Tx (..),
    WitnessSetHKD (..),
    addrWits',
  )
import Shelley.Spec.Ledger.TxBody
  ( witKeyHash,
  )

-- =================================================================
-- We translate a MultiSig by deserializing its bytes as a Timelock
-- If this succeeds (and it should, we designed Timelock to have
-- that property), then both version should have the same bytes,
-- because we are using FromCBOR(Annotator Timelock) instance.

translate :: CC.Crypto crypto => MultiSig crypto -> Timelock crypto
translate multi =
  let bytes = Lazy.fromStrict (fromShort (getMultiSigBytes multi))
   in case deserialiseFromBytes fromCBOR bytes of
        Left err -> error ("Translating MultiSig script to Timelock script fails\n" ++ show err)
        Right (left, Annotator f) | left == Lazy.empty -> f (Full bytes)
        Right (left, _) -> error ("Translating MultiSig script to Timelock script does not consume all they bytes: " ++ show left)

-- ================================================================
-- An pair of optional SlotNo.

-- | ValidityInterval is a half open interval. Closed on the bottom, Open on the top.
--   A SNothing on the bottom is negative infinity, and a SNothing on the top is positive infinity
data ValidityInterval = ValidityInterval
  { invalidBefore :: !(StrictMaybe SlotNo),
    invalidHereafter :: !(StrictMaybe SlotNo)
  }
  deriving (Ord, Eq, Generic, Show, NoThunks, NFData)

encodeVI :: ValidityInterval -> Encode ('Closed 'Dense) ValidityInterval
encodeVI (ValidityInterval f t) = Rec ValidityInterval !> To f !> To t

instance ToCBOR ValidityInterval where
  toCBOR vi = encode (encodeVI vi)

decodeVI :: Decode ('Closed 'Dense) ValidityInterval
decodeVI = RecD ValidityInterval <! From <! From

instance FromCBOR ValidityInterval where
  fromCBOR = decode decodeVI

-- ==================================================================

data TimelockRaw crypto
  = Signature !(KeyHash 'Witness crypto)
  | AllOf !(StrictSeq (Timelock crypto)) -- NOTE that Timelock and
  | AnyOf !(StrictSeq (Timelock crypto)) -- TimelockRaw are mutually recursive.
  | MOfN !Int !(StrictSeq (Timelock crypto)) -- Note that the Int may be negative in which case (MOfN -2 [..]) is always True
  | TimeStart !SlotNo -- The start time
  | TimeExpire !SlotNo -- The time it expires
  deriving (Eq, Show, Ord, Generic, NFData)

deriving instance Typeable crypto => NoThunks (TimelockRaw crypto)

-- These coding choices are chosen so that a MultiSig script
-- can be deserialised as a Timelock script

encRaw :: CC.Crypto crypto => TimelockRaw crypto -> Encode 'Open (TimelockRaw crypto)
encRaw (Signature hash) = Sum Signature 0 !> To hash
encRaw (AllOf xs) = Sum AllOf 1 !> E encodeFoldable xs
encRaw (AnyOf xs) = Sum AnyOf 2 !> E encodeFoldable xs
encRaw (MOfN m xs) = Sum MOfN 3 !> To m !> E encodeFoldable xs
encRaw (TimeStart m) = Sum TimeStart 4 !> To m
encRaw (TimeExpire m) = Sum TimeExpire 5 !> To m

decRaw :: CC.Crypto crypto => Word -> Decode 'Open (Annotator (TimelockRaw crypto))
decRaw 0 = Ann (SumD Signature <! From)
decRaw 1 = Ann (SumD AllOf) <*! D (sequence <$> decodeStrictSeq fromCBOR)
decRaw 2 = Ann (SumD AnyOf) <*! D (sequence <$> decodeStrictSeq fromCBOR)
decRaw 3 = Ann (SumD MOfN) <*! Ann From <*! D (sequence <$> decodeStrictSeq fromCBOR)
decRaw 4 = Ann (SumD TimeStart <! From)
decRaw 5 = Ann (SumD TimeExpire <! From)
decRaw n = Invalid n

-- This instance allows us to derive instance FromCBOR(Annotator (Timelock crypto)).
-- Since Timelock is a newtype around (Memo (Timelock crypto)).

instance CC.Crypto crypto => FromCBOR (Annotator (TimelockRaw crypto)) where
  fromCBOR = decode (Summands "TimelockRaw" decRaw)

-- =================================================================
-- Native Scripts are Memoized TimelockRaw.
-- The patterns give the appearence that the mutual recursion is not present.
-- They rely on memoBytes, and TimelockRaw to memoize each constructor of Timelock
-- =================================================================

newtype Timelock crypto = TimelockConstr (MemoBytes (TimelockRaw crypto))
  deriving (Eq, Ord, Show, Generic)
  deriving newtype (ToCBOR, NoThunks, NFData, SafeToHash)

deriving via
  Mem (TimelockRaw crypto)
  instance
    CC.Crypto crypto => FromCBOR (Annotator (Timelock crypto))

pattern RequireSignature :: CC.Crypto crypto => KeyHash 'Witness crypto -> Timelock crypto
pattern RequireSignature akh <-
  TimelockConstr (Memo (Signature akh) _)
  where
    RequireSignature akh =
      TimelockConstr $ memoBytes (encRaw (Signature akh))

pattern RequireAllOf :: CC.Crypto crypto => StrictSeq (Timelock crypto) -> Timelock crypto
pattern RequireAllOf ms <-
  TimelockConstr (Memo (AllOf ms) _)
  where
    RequireAllOf ms =
      TimelockConstr $ memoBytes (encRaw (AllOf ms))

pattern RequireAnyOf :: CC.Crypto crypto => StrictSeq (Timelock crypto) -> Timelock crypto
pattern RequireAnyOf ms <-
  TimelockConstr (Memo (AnyOf ms) _)
  where
    RequireAnyOf ms =
      TimelockConstr $ memoBytes (encRaw (AnyOf ms))

pattern RequireMOf :: CC.Crypto crypto => Int -> StrictSeq (Timelock crypto) -> Timelock crypto
pattern RequireMOf n ms <-
  TimelockConstr (Memo (MOfN n ms) _)
  where
    RequireMOf n ms =
      TimelockConstr $ memoBytes (encRaw (MOfN n ms))

pattern RequireTimeExpire :: CC.Crypto crypto => SlotNo -> Timelock crypto
pattern RequireTimeExpire mslot <-
  TimelockConstr (Memo (TimeExpire mslot) _)
  where
    RequireTimeExpire mslot =
      TimelockConstr $ memoBytes (encRaw (TimeExpire mslot))

pattern RequireTimeStart :: CC.Crypto crypto => SlotNo -> Timelock crypto
pattern RequireTimeStart mslot <-
  TimelockConstr (Memo (TimeStart mslot) _)
  where
    RequireTimeStart mslot =
      TimelockConstr $ memoBytes (encRaw (TimeStart mslot))

{-# COMPLETE RequireSignature, RequireAllOf, RequireAnyOf, RequireMOf, RequireTimeExpire, RequireTimeStart #-}

-- =================================================================
-- Evaluating and validating a Timelock

-- | less-than-equal comparison, where Nothing is negative infinity
lteNegInfty :: SlotNo -> StrictMaybe SlotNo -> Bool
lteNegInfty _ SNothing = False -- i > -∞
lteNegInfty i (SJust j) = i <= j

-- | less-than-equal comparison, where Nothing is positive infinity
ltePosInfty :: StrictMaybe SlotNo -> SlotNo -> Bool
ltePosInfty SNothing _ = False -- ∞ > j
ltePosInfty (SJust i) j = i <= j

evalTimelock ::
  CC.Crypto crypto =>
  Set (KeyHash 'Witness crypto) ->
  ValidityInterval ->
  Timelock crypto ->
  Bool
evalTimelock _vhks (ValidityInterval txStart _) (RequireTimeStart lockStart) =
  lockStart `lteNegInfty` txStart
evalTimelock _vhks (ValidityInterval _ txExp) (RequireTimeExpire lockExp) =
  txExp `ltePosInfty` lockExp
evalTimelock vhks _vi (RequireSignature hash) = member hash vhks
evalTimelock vhks vi (RequireAllOf xs) =
  all (evalTimelock vhks vi) xs
evalTimelock vhks vi (RequireAnyOf xs) =
  any (evalTimelock vhks vi) xs
evalTimelock vhks vi (RequireMOf m xs) =
  m <= sum (fmap (\x -> if evalTimelock vhks vi x then 1 else 0) xs)

-- =========================================================
-- Operations on Timelock scripts

-- | Test if a slot is in the Validity interval. Recall that a ValidityInterval
--   is a half Open interval, that is why we use (slot < top)
inInterval :: SlotNo -> ValidityInterval -> Bool
inInterval _slot (ValidityInterval SNothing SNothing) = True
inInterval slot (ValidityInterval SNothing (SJust top)) = slot < top
inInterval slot (ValidityInterval (SJust bottom) SNothing) = bottom <= slot
inInterval slot (ValidityInterval (SJust bottom) (SJust top)) =
  bottom <= slot && slot < top

-- =======================================================
-- Validating timelock scripts
-- We Assume that TxBody has field "vldt" that extracts a ValidityInterval
-- We still need to correctly compute the witness set for Core.TxBody as well.

evalFPS ::
  forall era.
  ( Era era,
    HasField "vldt" (Core.TxBody era) ValidityInterval
  ) =>
  Timelock (Crypto era) ->
  Set (KeyHash 'Witness (Crypto era)) ->
  Core.TxBody era ->
  Bool
evalFPS timelock vhks txb = evalTimelock vhks (getField @"vldt" txb) timelock

validateTimelock ::
  forall era.
  ( UsesTxBody era,
    UsesScript era,
    HasField "vldt" (Core.TxBody era) ValidityInterval,
    ToCBOR (Core.AuxiliaryData era)
  ) =>
  Timelock (Crypto era) ->
  Tx era ->
  Bool
validateTimelock lock tx = evalFPS @era lock vhks (_body tx)
  where
    -- THIS IS JUST A STUB. WHO KNOWS IF
    witsSet = _witnessSet tx -- IT COMPUTES THE RIGHT WITNESS SET.
    vhks = Set.map witKeyHash (addrWits' witsSet)

showTimelock :: CC.Crypto crypto => Timelock crypto -> String
showTimelock (RequireTimeStart (SlotNo i)) = "(Start >= " ++ show i ++ ")"
showTimelock (RequireTimeExpire (SlotNo i)) = "(Expire < " ++ show i ++ ")"
showTimelock (RequireAllOf xs) = "(AllOf " ++ foldl accum ")" xs
  where
    accum ans x = showTimelock x ++ " " ++ ans
showTimelock (RequireAnyOf xs) = "(AnyOf " ++ foldl accum ")" xs
  where
    accum ans x = showTimelock x ++ " " ++ ans
showTimelock (RequireMOf m xs) = "(MOf " ++ show m ++ " " ++ foldl accum ")" xs
  where
    accum ans x = showTimelock x ++ " " ++ ans
showTimelock (RequireSignature hash) = "(Signature " ++ show hash ++ ")"

-- ===============================================================
-- Pretty Printer

ppTimelock :: Timelock crypto -> PDoc
ppTimelock (TimelockConstr (Memo (Signature akh) _)) =
  ppSexp "Signature" [ppKeyHash akh]
ppTimelock (TimelockConstr (Memo (AllOf ms) _)) =
  ppSexp "AllOf" (foldr (:) [] (fmap ppTimelock ms))
ppTimelock (TimelockConstr (Memo (AnyOf ms) _)) =
  ppSexp "AnyOf" (foldr (:) [] (fmap ppTimelock ms))
ppTimelock (TimelockConstr (Memo (MOfN m ms) _)) =
  ppSexp "MOfN" (ppInteger (fromIntegral m) : (foldr (:) [] (fmap ppTimelock ms)))
ppTimelock (TimelockConstr (Memo (TimeExpire mslot) _)) =
  ppSexp "Expires" [ppSlotNo mslot]
ppTimelock (TimelockConstr (Memo (TimeStart mslot) _)) =
  ppSexp "Starts" [ppSlotNo mslot]

instance PrettyA (Timelock crypto) where prettyA = ppTimelock

ppValidityInterval :: ValidityInterval -> PDoc
ppValidityInterval (ValidityInterval b a) =
  ppRecord
    "ValidityInterval"
    [ ("invalidBefore", ppStrictMaybe ppSlotNo b),
      ("invalidHereafter", ppStrictMaybe ppSlotNo a)
    ]

instance PrettyA ValidityInterval where prettyA = ppValidityInterval
