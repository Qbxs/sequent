module Interpretation where

import Prop

import Data.List (intercalate)
import qualified Data.Set as S

-- | Interpretation to extract
data Interpretation
  = Interpretation
     { false :: S.Set Char
     , true :: S.Set Char
     }

instance Semigroup Interpretation where
  (<>) l r = Interpretation (false l `S.union` false r) (true l `S.union` true r)

instance Monoid Interpretation where
  mempty = Interpretation S.empty S.empty

instance Render Interpretation where
  render i = ('\t':) $! intercalate ", " $!
                map (\c -> "I(" <> pure c <> ")=t") (S.toList $ true i)
             <> map (\c -> "I(" <> pure c <> ")=f") (S.toList $ false i)
