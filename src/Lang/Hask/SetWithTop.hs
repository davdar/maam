module Lang.Hask.SetWithTop where

import FP

data SetWithTop a =
    SetTop
  | SetNotTop (Set a)

setWithTopElim :: b -> (Set a -> b) -> SetWithTop a -> b
setWithTopElim b _ SetTop = b
setWithTopElim _ f (SetNotTop x) = f x

instance Bot (SetWithTop a) where bot = SetNotTop empty
instance Join (SetWithTop a) where
  SetTop \/ _ = SetTop
  _ \/ SetTop = SetTop
  SetNotTop x \/ SetNotTop y = SetNotTop $ x \/ y
instance JoinLattice (SetWithTop a)
instance Top (SetWithTop a) where top = SetTop
instance Meet (SetWithTop a) where
  SetTop /\ x = x
  x /\ SetTop = x
  SetNotTop x /\ SetNotTop y = SetNotTop $ x /\ y
instance MeetLattice (SetWithTop a)

setWithTopInject :: (Ord a) => a -> SetWithTop a
setWithTopInject = SetNotTop . single

fromListWithTop :: (Ord a) => ListWithTop a -> SetWithTop a
fromListWithTop ListTop = SetTop
fromListWithTop (ListNotTop xs) = SetNotTop $ fromList $ toList xs

data ListWithTop a =
    ListTop
  | ListNotTop (ListSet a)

instance Bot (ListWithTop a) where bot = ListNotTop nil
instance Join (ListWithTop a) where
  ListTop \/ _ = ListTop
  _ \/ ListTop = ListTop
  ListNotTop x \/ ListNotTop y = ListNotTop $ x ++ y
instance JoinLattice (ListWithTop a)
instance Top (ListWithTop a) where top = ListTop
instance Meet (ListWithTop a) where
  ListTop /\ x = x
  x /\ ListTop = x
  ListNotTop x /\ ListNotTop y = ListNotTop $ x ++ y
instance MeetLattice (ListWithTop a)

instance MonadBot ListWithTop where mbot = bot
instance MonadPlus ListWithTop where (<+>) = (\/)
instance MonadTop ListWithTop where mtop = top

instance MonadAppend ListWithTop where (<++>) = (\/)

instance Unit ListWithTop where unit = ListNotTop . single
instance Bind ListWithTop where
  ListTop >>= _ = ListTop
  ListNotTop xs >>= f = joins $ map f xs
instance Functor ListWithTop where map = mmap
instance Product ListWithTop where (<*>) = mpair
instance Applicative ListWithTop where (<@>) = mapply
instance Monad ListWithTop
