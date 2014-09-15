module FP.ErrorListExamples where

import FP

ex1 :: ErrorListT String ID Int
ex1 = ErrorListT $ ID $ ErrorListFailure ["bad1", "bad2"]

ex1i :: ErrorListT String (ErrorListT String ID) Int
ex1i = errorListI ex1

ex1ie :: ErrorT String (ErrorListT String ID) Int
ex1ie = errorListToError ex1i

ex1it :: ErrorListT String (ErrorListT String ID) Int
ex1it = errorListCommute ex1i

ex1itt :: ErrorListT String (ErrorListT String ID) Int
ex1itt = errorListCommute ex1it

ex2 :: ErrorListT String ID Int
ex2 = unit 1 ++ unit 2 ++ unit 3

ex2i :: ErrorListT String (ErrorListT String ID) Int
ex2i = errorListI ex2

ex2it :: ErrorListT String (ErrorListT String ID) Int
ex2it = errorListCommute ex2i

ex2itt :: ErrorListT String (ErrorListT String ID) Int
ex2itt = errorListCommute ex2it
