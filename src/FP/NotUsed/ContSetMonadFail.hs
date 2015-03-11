newtype FooSet r a = FooSet { unFooSet :: (a -> Set r) -> Set r }
runFooSet :: (Ord r) => FooSet r r -> Set r
runFooSet x = unFooSet x singleton

instance Unit (FooSet r) where
  unit a = FooSet $ \ k -> k a
instance Bind (FooSet r) where
  FooSet (ak :: (a -> Set r) -> Set r) >>= (f :: a -> FooSet r b) = FooSet $ \ (k :: b -> Set r) ->
    ak $ \ a -> unFooSet (f a) k
instance Functor (FooSet r) where map = mmap
instance Product (FooSet r) where (<*>) = mpair
instance Applicative (FooSet r) where (<@>) = mapply
instance Monad (FooSet r)

instance MonadZero (FooSet r) where
  mzero = FooSet $ \ _ -> empty
instance MonadPlus (FooSet r) where
  FooSet (ak₁ :: (a -> Set r) -> Set r) <+> FooSet (ak₂ :: (a -> Set r) -> Set r) = FooSet $ \ (k :: a -> Set r) -> do
    ak₁ $ \ a₁ -> ak₂ $ \ a₂ -> k a₁ \/ k a₂
    
test :: Set Int
test = runFooSet $ do
  x <- return 1 <+> mzero
  y <- return 4 <+> return 5
  return $ x + y
