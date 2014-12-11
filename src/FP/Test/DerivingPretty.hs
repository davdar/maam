module FP.Test.DerivingPretty where

import FP
import FP.DerivingPretty

data AS a = FooAS Int | BarAS a
makePrettySum ''AS

data AU a = FooAU Int | BarAU a
makePrettyUnion ''AU

data BS a b = FooBS Int | BarBS a b
makePrettySum ''BS

data BU a b = FooBU Int | BarBU a b
makePrettyUnion ''BU

xas, yas :: AS String
xas = FooAS 1
yas = BarAS "hi"

xau, yau :: AU String
xau = FooAU 1
yau = BarAU "hi"

xbs, ybs :: BS String (Int, Int)
xbs = FooBS 1
ybs = BarBS "hi" (1, 2)

xbu, ybu :: BU String (Int, Int)
xbu = FooBU 1
ybu = BarBU "hi" (1, 2)
