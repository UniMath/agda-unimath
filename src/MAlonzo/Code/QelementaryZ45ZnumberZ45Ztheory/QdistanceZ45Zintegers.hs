{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.distance-integers.dist-ℤ
d_dist'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Integer
d_dist'45'ℤ_4 v0 v1
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_abs'45'ℤ_4
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
         (coe v0) (coe v1))
-- elementary-number-theory.distance-integers.ap-dist-ℤ
d_ap'45'dist'45'ℤ_22 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'dist'45'ℤ_22 = erased
-- elementary-number-theory.distance-integers.left-zero-law-dist-ℤ
d_left'45'zero'45'law'45'dist'45'ℤ_30 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'zero'45'law'45'dist'45'ℤ_30 = erased
-- elementary-number-theory.distance-integers.right-zero-law-dist-ℤ
d_right'45'zero'45'law'45'dist'45'ℤ_36 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'zero'45'law'45'dist'45'ℤ_36 = erased
-- elementary-number-theory.distance-integers.dist-int-ℕ
d_dist'45'int'45'ℕ_44 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_dist'45'int'45'ℕ_44 = erased
