module FP
  ( module FP.Console
  , module FP.Core
  , module FP.DerivingLens
  , module FP.DerivingPrism
  , module FP.DerivingMonoid
  , module FP.DerivingJoinLattice
  , module FP.DerivingPretty
  , module FP.Free
  , module FP.Monads
  , module FP.Pretty
  , module FP.IO
  -- , module FP
  ) where

import FP.Console (pprint, pprintDoc, ptrace, pprintWith, pprintWidth)
import FP.Core
import FP.DerivingLens
import FP.DerivingPrism
import FP.Free
import FP.Monads
import FP.Pretty (Pretty(..), Doc, DocM, ptoString)
import FP.DerivingMonoid
import FP.DerivingJoinLattice
import FP.DerivingPretty
import FP.IO
import FP.Compat ()

-- newtype M s a = M { unM :: s -> Map a s }
-- runM :: s -> M s a -> Map a s
-- runM = flip unM
-- 
-- mreturn :: (Ord a) => a -> M s a
-- mreturn a = M $ \ s -> single (a, s)
-- 
-- (>>>=) :: (JoinLattice s) => M s a -> (a -> M s b) -> M s b
-- aM >>>= f = M $ \ s -> joins $ map (uncurry $ unM . f) $ toList $ unM aM s
-- 
-- mmzero :: M s a
-- mmzero = M $ const mapEmpty
-- 
-- (<<+>>) :: (Join s) => M s a -> M s a -> M s a
-- aM1 <<+>> aM2 = M $ \ s -> unM aM1 s \/ unM aM2 s
-- 
-- mget :: (Ord s) => M s s
-- mget = M $ \ s -> single (s, s)
-- 
-- mput :: s -> M s ()
-- mput s = M $ \ _ -> single ((), s)
-- 
-- p1 :: M Int Int
-- p1 = mreturn 1 <<+>> mreturn 2
-- 
-- p2 :: M Int Int
-- p2 = p1 >>>= \ x ->
--      mget >>>= \ s ->
--      mput (x + s) >>>= \ () ->
--      mreturn x
