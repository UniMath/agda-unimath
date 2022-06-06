{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- foundation-core.truncation-levels.𝕋
d_𝕋_4 = ()
data T_𝕋_4 = C_neg'45'two'45'𝕋_6 | C_succ'45'𝕋_8 T_𝕋_4
-- foundation-core.truncation-levels.neg-one-𝕋
d_neg'45'one'45'𝕋_10 :: T_𝕋_4
d_neg'45'one'45'𝕋_10 = coe C_succ'45'𝕋_8 (coe C_neg'45'two'45'𝕋_6)
-- foundation-core.truncation-levels.zero-𝕋
d_zero'45'𝕋_12 :: T_𝕋_4
d_zero'45'𝕋_12 = coe C_succ'45'𝕋_8 (coe d_neg'45'one'45'𝕋_10)
-- foundation-core.truncation-levels.one-𝕋
d_one'45'𝕋_14 :: T_𝕋_4
d_one'45'𝕋_14 = coe C_succ'45'𝕋_8 (coe d_zero'45'𝕋_12)
-- foundation-core.truncation-levels.two-𝕋
d_two'45'𝕋_16 :: T_𝕋_4
d_two'45'𝕋_16 = coe C_succ'45'𝕋_8 (coe d_one'45'𝕋_14)
