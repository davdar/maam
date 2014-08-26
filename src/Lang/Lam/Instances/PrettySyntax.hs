module Lang.Lam.Instances.PrettySyntax where

import FP
import Lang.Lam.Syntax
import qualified FP.Pretty as P

instance Pretty LocNum where
  pretty (LocNum i) = P.pun $ ptoString i
instance Pretty BdrNum where
  pretty (BdrNum i) = P.format (P.setFG 2) $ P.text $ ptoString i
instance Pretty Name where
  pretty (Name s) = P.bdr s
instance Pretty GName where
  pretty (GName iM s) = do
    pretty s
    maybeOn iM (return ()) $ \ i -> do
      P.pun "#"
      P.pun $ toString i
instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
instance Pretty Op where
  pretty Add1 = P.key "+1"
  pretty Sub1 = P.key "-1"
  pretty IsNonNeg = P.key ">=0?"
