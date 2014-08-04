newtype NondetT m a = NondetT { runNondetT :: m [a] }
