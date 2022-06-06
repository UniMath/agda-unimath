{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps

-- elementary-number-theory.multiplication-integers.mul-ℤ
d_mul'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_mul'45'ℤ_4 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v2 of
             0 -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                    (coe v1)
             _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_add'45'ℤ_4
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                       (coe v1))
                    (coe
                       d_mul'45'ℤ_4
                       (coe
                          MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v3))
                       (coe v1))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    0 -> coe v1
                    _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_add'45'ℤ_4
                           (coe v1)
                           (coe
                              d_mul'45'ℤ_4
                              (coe
                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                 (coe
                                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v4)))
                              (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.multiplication-integers.mul-ℤ'
d_mul'45'ℤ''_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_mul'45'ℤ''_20 v0 v1 = coe d_mul'45'ℤ_4 (coe v1) (coe v0)
-- elementary-number-theory.multiplication-integers.ap-mul-ℤ
d_ap'45'mul'45'ℤ_34 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'mul'45'ℤ_34 = erased
-- elementary-number-theory.multiplication-integers.explicit-mul-ℤ
d_explicit'45'mul'45'ℤ_40 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_explicit'45'mul'45'ℤ_40 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                       (coe addInt (coe (1 :: Integer)) (coe v2))
                       (coe addInt (coe (1 :: Integer)) (coe v3)))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                           (coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                              (coe
                                 MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                                 (coe addInt (coe (1 :: Integer)) (coe v2))
                                 (coe addInt (coe (1 :: Integer)) (coe v4))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> case coe v1 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe
                           seq (coe v4)
                           (coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v1 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                           (coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                              (coe
                                 MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                                 (coe addInt (coe (1 :: Integer)) (coe v3))
                                 (coe addInt (coe (1 :: Integer)) (coe v4))))
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> case coe v4 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> coe
                                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> coe
                                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                                  (coe
                                     MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                                     (coe addInt (coe (1 :: Integer)) (coe v3))
                                     (coe addInt (coe (1 :: Integer)) (coe v5)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.multiplication-integers.explicit-mul-ℤ'
d_explicit'45'mul'45'ℤ''_66 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_explicit'45'mul'45'ℤ''_66 v0 v1
  = coe d_explicit'45'mul'45'ℤ_40 (coe v1) (coe v0)
-- elementary-number-theory.multiplication-integers.left-zero-law-mul-ℤ
d_left'45'zero'45'law'45'mul'45'ℤ_74 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'zero'45'law'45'mul'45'ℤ_74 = erased
-- elementary-number-theory.multiplication-integers.right-zero-law-mul-ℤ
d_right'45'zero'45'law'45'mul'45'ℤ_80 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'zero'45'law'45'mul'45'ℤ_80 = erased
-- elementary-number-theory.multiplication-integers.left-unit-law-mul-ℤ
d_left'45'unit'45'law'45'mul'45'ℤ_88 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'mul'45'ℤ_88 = erased
-- elementary-number-theory.multiplication-integers.right-unit-law-mul-ℤ
d_right'45'unit'45'law'45'mul'45'ℤ_94 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'mul'45'ℤ_94 = erased
-- elementary-number-theory.multiplication-integers.left-neg-unit-law-mul-ℤ
d_left'45'neg'45'unit'45'law'45'mul'45'ℤ_102 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'neg'45'unit'45'law'45'mul'45'ℤ_102 = erased
-- elementary-number-theory.multiplication-integers.right-neg-unit-law-mul-ℤ
d_right'45'neg'45'unit'45'law'45'mul'45'ℤ_108 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'neg'45'unit'45'law'45'mul'45'ℤ_108 = erased
-- elementary-number-theory.multiplication-integers.left-successor-law-mul-ℤ
d_left'45'successor'45'law'45'mul'45'ℤ_118 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'mul'45'ℤ_118 = erased
-- elementary-number-theory.multiplication-integers.left-predecessor-law-mul-ℤ
d_left'45'predecessor'45'law'45'mul'45'ℤ_136 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'predecessor'45'law'45'mul'45'ℤ_136 = erased
-- elementary-number-theory.multiplication-integers.right-successor-law-mul-ℤ
d_right'45'successor'45'law'45'mul'45'ℤ_154 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'mul'45'ℤ_154 = erased
-- elementary-number-theory.multiplication-integers.right-predecessor-law-mul-ℤ
d_right'45'predecessor'45'law'45'mul'45'ℤ_174 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'predecessor'45'law'45'mul'45'ℤ_174 = erased
-- elementary-number-theory.multiplication-integers.right-distributive-mul-add-ℤ
d_right'45'distributive'45'mul'45'add'45'ℤ_196 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'distributive'45'mul'45'add'45'ℤ_196 = erased
-- elementary-number-theory.multiplication-integers.left-negative-law-mul-ℤ
d_left'45'negative'45'law'45'mul'45'ℤ_226 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'negative'45'law'45'mul'45'ℤ_226 = erased
-- elementary-number-theory.multiplication-integers.associative-mul-ℤ
d_associative'45'mul'45'ℤ_248 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'mul'45'ℤ_248 = erased
-- elementary-number-theory.multiplication-integers.commutative-mul-ℤ
d_commutative'45'mul'45'ℤ_278 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'mul'45'ℤ_278 = erased
-- elementary-number-theory.multiplication-integers.left-distributive-mul-add-ℤ
d_left'45'distributive'45'mul'45'add'45'ℤ_300 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'distributive'45'mul'45'add'45'ℤ_300 = erased
-- elementary-number-theory.multiplication-integers.right-negative-law-mul-ℤ
d_right'45'negative'45'law'45'mul'45'ℤ_312 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'negative'45'law'45'mul'45'ℤ_312 = erased
-- elementary-number-theory.multiplication-integers.interchange-law-mul-mul-ℤ
d_interchange'45'law'45'mul'45'mul'45'ℤ_318 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_interchange'45'law'45'mul'45'mul'45'ℤ_318 = erased
-- elementary-number-theory.multiplication-integers.is-mul-neg-one-neg-ℤ
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ_322 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ_322 = erased
-- elementary-number-theory.multiplication-integers.is-mul-neg-one-neg-ℤ'
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ''_328 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ''_328 = erased
-- elementary-number-theory.multiplication-integers.is-positive-mul-ℤ
d_is'45'positive'45'mul'45'ℤ_336 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'positive'45'mul'45'ℤ_336 = erased
-- elementary-number-theory.multiplication-integers.mul-int-ℕ
d_mul'45'int'45'ℕ_356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mul'45'int'45'ℕ_356 = erased
-- elementary-number-theory.multiplication-integers.compute-mul-ℤ
d_compute'45'mul'45'ℤ_368 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compute'45'mul'45'ℤ_368 = erased
-- elementary-number-theory.multiplication-integers.linear-diff-ℤ
d_linear'45'diff'45'ℤ_408 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_linear'45'diff'45'ℤ_408 = erased
-- elementary-number-theory.multiplication-integers.linear-diff-ℤ'
d_linear'45'diff'45'ℤ''_422 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_linear'45'diff'45'ℤ''_422 = erased
-- elementary-number-theory.multiplication-integers.is-zero-is-zero-mul-ℤ
d_is'45'zero'45'is'45'zero'45'mul'45'ℤ_434 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'zero'45'is'45'zero'45'mul'45'ℤ_434 v0 v1 ~v2
  = du_is'45'zero'45'is'45'zero'45'mul'45'ℤ_434 v0 v1
du_is'45'zero'45'is'45'zero'45'mul'45'ℤ_434 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'zero'45'is'45'zero'45'mul'45'ℤ_434 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                    erased
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe
                           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v1 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                           erased
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> case coe v4 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> coe
                                  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                  erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.multiplication-integers.is-injective-mul-ℤ
d_is'45'injective'45'mul'45'ℤ_474 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'ℤ_474 = erased
-- elementary-number-theory.multiplication-integers.is-injective-mul-ℤ'
d_is'45'injective'45'mul'45'ℤ''_488 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'ℤ''_488 = erased
-- elementary-number-theory.multiplication-integers.is-emb-mul-ℤ
d_is'45'emb'45'mul'45'ℤ_502 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'mul'45'ℤ_502 ~v0 ~v1 = du_is'45'emb'45'mul'45'ℤ_502
du_is'45'emb'45'mul'45'ℤ_502 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'mul'45'ℤ_502
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.multiplication-integers.is-emb-mul-ℤ'
d_is'45'emb'45'mul'45'ℤ''_510 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'mul'45'ℤ''_510 ~v0 ~v1
  = du_is'45'emb'45'mul'45'ℤ''_510
du_is'45'emb'45'mul'45'ℤ''_510 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'mul'45'ℤ''_510
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.multiplication-integers.is-positive-left-factor-mul-ℤ
d_is'45'positive'45'left'45'factor'45'mul'45'ℤ_520 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'positive'45'left'45'factor'45'mul'45'ℤ_520 = erased
-- elementary-number-theory.multiplication-integers.is-positive-right-factor-mul-ℤ
d_is'45'positive'45'right'45'factor'45'mul'45'ℤ_548 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'positive'45'right'45'factor'45'mul'45'ℤ_548 = erased
-- elementary-number-theory.multiplication-integers.is-nonnegative-mul-ℤ
d_is'45'nonnegative'45'mul'45'ℤ_560 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'nonnegative'45'mul'45'ℤ_560 = erased
-- elementary-number-theory.multiplication-integers.is-nonnegative-left-factor-mul-ℤ
d_is'45'nonnegative'45'left'45'factor'45'mul'45'ℤ_586 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'nonnegative'45'left'45'factor'45'mul'45'ℤ_586 = erased
-- elementary-number-theory.multiplication-integers.is-nonnegative-right-factor-mul-ℤ
d_is'45'nonnegative'45'right'45'factor'45'mul'45'ℤ_608 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'nonnegative'45'right'45'factor'45'mul'45'ℤ_608 = erased
-- elementary-number-theory.multiplication-integers.preserves-leq-mul-ℤ
d_preserves'45'leq'45'mul'45'ℤ_622 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_preserves'45'leq'45'mul'45'ℤ_622 = erased
-- elementary-number-theory.multiplication-integers.preserves-leq-mul-ℤ'
d_preserves'45'leq'45'mul'45'ℤ''_650 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_preserves'45'leq'45'mul'45'ℤ''_650 = erased
