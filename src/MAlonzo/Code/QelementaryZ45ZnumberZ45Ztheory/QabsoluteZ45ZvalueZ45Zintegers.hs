{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.absolute-value-integers.abs-ℤ
d_abs'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Integer
d_abs'45'ℤ_4 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe addInt (coe (1 :: Integer)) (coe v1)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
               -> coe (0 :: Integer)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
               -> coe addInt (coe (1 :: Integer)) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.absolute-value-integers.int-abs-ℤ
d_int'45'abs'45'ℤ_10 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_int'45'abs'45'ℤ_10
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v0 ->
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36))
      (coe d_abs'45'ℤ_4)
-- elementary-number-theory.absolute-value-integers.abs-int-ℕ
d_abs'45'int'45'ℕ_14 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_abs'45'int'45'ℕ_14 = erased
-- elementary-number-theory.absolute-value-integers.abs-neg-ℤ
d_abs'45'neg'45'ℤ_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_abs'45'neg'45'ℤ_20 = erased
-- elementary-number-theory.absolute-value-integers.eq-abs-ℤ
d_eq'45'abs'45'ℤ_28 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'abs'45'ℤ_28 = erased
-- elementary-number-theory.absolute-value-integers.abs-eq-ℤ
d_abs'45'eq'45'ℤ_34 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_abs'45'eq'45'ℤ_34 = erased
-- elementary-number-theory.absolute-value-integers.predecessor-law-abs-ℤ
d_predecessor'45'law'45'abs'45'ℤ_38 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_predecessor'45'law'45'abs'45'ℤ_38 = erased
-- elementary-number-theory.absolute-value-integers.successor-law-abs-ℤ
d_successor'45'law'45'abs'45'ℤ_46 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_successor'45'law'45'abs'45'ℤ_46 = erased
-- elementary-number-theory.absolute-value-integers.subadditive-abs-ℤ
d_subadditive'45'abs'45'ℤ_56 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_subadditive'45'abs'45'ℤ_56 = erased
-- elementary-number-theory.absolute-value-integers.negative-law-abs-ℤ
d_negative'45'law'45'abs'45'ℤ_74 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_negative'45'law'45'abs'45'ℤ_74 = erased
-- elementary-number-theory.absolute-value-integers.is-positive-abs-ℤ
d_is'45'positive'45'abs'45'ℤ_82 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_is'45'positive'45'abs'45'ℤ_82 = erased
-- elementary-number-theory.absolute-value-integers.is-nonzero-abs-ℤ
d_is'45'nonzero'45'abs'45'ℤ_90 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'abs'45'ℤ_90 = erased
