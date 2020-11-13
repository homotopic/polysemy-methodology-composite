{- |
   Module     : Polysemy.Methodology.Composite
   License    : MIT
   Maintainer : dan.firth@homotopic.tech
   Stability  : experimental

Functions for combining polysemy-methodology with composite.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Polysemy.Methodology.Composite (
  runCoRecMethodologyAsCases
, runCoRecMethodologyAsCases'
, diffractMethodology
, diffractMethodology'
) where

import Control.Arrow
import Composite.CoRecord
import Data.Vinyl
import Polysemy
import Polysemy.Extra
import Polysemy.Input
import Polysemy.Methodology

-- | Run a `Methodology` from a `CoRec` to an `Input` of `Cases'`. You can then use `Polysemy.Vinyl.separateRecInput` and `Polysemy.Vinyl.stripRecInput`
-- to deal with the cases individually.
--
-- @since 0.1.0.0
runCoRecMethodologyAsCases :: forall f zs c x xs r a.
                              (zs ~ (x ': xs), RecApplicative zs, Members '[Input (Cases' f zs c)] r)
                           => Sem (Methodology (CoRec f zs) c ': r) a
                              -- ^ The Methodology to decompose.
                           -> Sem r a
runCoRecMethodologyAsCases = interpret \case
  Process b -> do
    x <- input @(Cases' f zs c)
    return $ foldCoRec x b
{-# INLINE runCoRecMethodologyAsCases #-}

-- | Reinterpreting version of `runCoRecMethodologyAsCases`.
--
--
-- @since 0.1.0.0
runCoRecMethodologyAsCases' :: forall f zs c x xs r a.
                               (zs ~ (x ': xs), RecApplicative zs)
                            => Sem (Methodology (CoRec f zs) c ': r) a
                               -- ^ The Methodology to decompose.
                            -> Sem (Input (Cases' f zs c) ': r) a
runCoRecMethodologyAsCases' = reinterpret \case
  Process b -> do
    x <- input @(Cases' f zs c)
    return $ foldCoRec x b
{-# INLINE runCoRecMethodologyAsCases' #-}

-- | Diffraction is a combination of a `cutMethodology'`, an `mconcatMethodology'` and a `runCoRecMethodologyAsCases`.
--
-- This effectively allows you to make several ad-hoc constructors for d and fully consumes the second half of the cut.
-- This turns out to be quite a good way to start a simple pipeline.
--
-- @since 0.1.0.0
diffractMethodology :: forall b f zs d x xs r a.
                       (Monoid d, zs ~ (x ': xs)
                      , RecApplicative zs
                      , Members '[ Methodology b [CoRec f zs]
                                 , Input (Cases' f zs d)] r)
                    => Sem (Methodology b d ': r) a
                       -- ^ The Methodology to decompose.
                    -> Sem r a
diffractMethodology = cutMethodology' @b @[CoRec f zs] @d
                  >>> reinterpretUnder mconcatMethodology'
                  >>> reinterpretUnder runCoRecMethodologyAsCases'
                  >>> subsume >>> subsume
{-# INLINE diffractMethodology #-}

-- | Reinterpreting version of `diffractMethodology`.
--
-- @since 0.1.0.0
diffractMethodology' :: forall b f zs d x xs r a.
                        (Monoid d, zs ~ (x ': xs), RecApplicative zs)
                     => Sem (Methodology b d ': r) a
                        -- ^ The Methodology to decompose.
                     -> Sem (Methodology b [CoRec f zs] ': Input (Cases' f zs d) ': r) a
diffractMethodology' = cutMethodology' @b @[CoRec f zs] @d
                   >>> reinterpretUnder mconcatMethodology'
                   >>> reinterpretUnder runCoRecMethodologyAsCases'
{-# INLINE diffractMethodology' #-}
