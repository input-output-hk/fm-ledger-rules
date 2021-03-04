{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.AuxiliaryData
  ( AuxiliaryDataHash (..),
    ValidateAuxiliaryData (..),
  )
where

import Cardano.Binary (FromCBOR, ToCBOR)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
-- import Cardano.Ledger.Era (Crypto)
import Cardano.Ledger.SafeHash
  ( EraIndependentAuxiliaryData,
    SafeHash,
  )
import Control.DeepSeq (NFData (..))
import NoThunks.Class (NoThunks (..))

newtype AuxiliaryDataHash crypto = AuxiliaryDataHash
  { unsafeAuxiliaryDataHash :: SafeHash crypto EraIndependentAuxiliaryData
  }
  deriving (Show, Eq, Ord, NoThunks, NFData)

deriving instance
  CC.Crypto crypto =>
  ToCBOR (AuxiliaryDataHash crypto)

deriving instance
  CC.Crypto crypto =>
  FromCBOR (AuxiliaryDataHash crypto)

class ValidateAuxiliaryData era c | era -> c where
  hashAuxiliaryData :: Core.AuxiliaryData era -> AuxiliaryDataHash c
  validateAuxiliaryData :: Core.AuxiliaryData era -> Bool
