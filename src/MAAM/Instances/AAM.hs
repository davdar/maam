module MAAM.Instances.AAM where

import FP
import MAAM.Classes.AAM
import MAAM.Instances.Temporal

--------------
-- Concrete --
--------------

data Cμ = Cμ
cμ :: P Cμ
cμ = P

instance AAM Cμ where
  type LexicalTemporal Cμ = Cτ
  type DynamicTemporal Cμ = Cτ
  lexical Cμ = Cτ
  dynamic Cμ = Cτ

----------
-- 0CFA --
----------

data ZCFAμ = ZCFAμ
zCFAμ :: P ZCFAμ
zCFAμ = P

instance AAM ZCFAμ where
  type LexicalTemporal ZCFAμ = Zτ
  type DynamicTemporal ZCFAμ = Zτ
  lexical ZCFAμ = Zτ
  dynamic ZCFAμ = Zτ

----------
-- kCFA --
----------

data KCFAμ = KCFAμ Int
kCFAμ :: P KCFAμ
kCFAμ = P

instance AAM KCFAμ where
  type LexicalTemporal KCFAμ = Zτ
  type DynamicTemporal KCFAμ = Kτ
  lexical (KCFAμ _) = Zτ
  dynamic (KCFAμ k) = Kτ k

------------------------
-- k-object-sensitive --
------------------------

data KOSμ = KOSμ Int
kOSμ :: P KOSμ
kOSμ = P

instance AAM KOSμ where
  type LexicalTemporal KOSμ = Kτ
  type DynamicTemporal KOSμ = Zτ
  lexical (KOSμ k) = Kτ k
  dynamic (KOSμ _) = Zτ

---------------------------------------------
-- Hybrid k-call-site + k-object-sensitive --
---------------------------------------------

data KHybridμ = KHybridμ Int Int
kHybridμ :: P KHybridμ
kHybridμ = P

instance AAM KHybridμ where
  type LexicalTemporal KHybridμ = Kτ
  type DynamicTemporal KHybridμ = Kτ
  lexical (KHybridμ lk _) = Kτ lk
  dynamic (KHybridμ _ dk) = Kτ dk
