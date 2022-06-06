{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.divisibility-integers.div-ℤ
d_div'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_div'45'ℤ_4 = erased
-- elementary-number-theory.divisibility-integers.refl-div-ℤ
d_refl'45'div'45'ℤ_14 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'div'45'ℤ_14 ~v0 = du_refl'45'div'45'ℤ_14
du_refl'45'div'45'ℤ_14 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'div'45'ℤ_14
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_one'45'ℤ_30)
      erased
-- elementary-number-theory.divisibility-integers.trans-div-ℤ
d_trans'45'div'45'ℤ_26 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trans'45'div'45'ℤ_26 ~v0 ~v1 ~v2 v3 v4
  = du_trans'45'div'45'ℤ_26 v3 v4
du_trans'45'div'45'ℤ_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trans'45'div'45'ℤ_26 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                       (coe v4) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.is-prop-div-ℤ
d_is'45'prop'45'div'45'ℤ_60 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'div'45'ℤ_60 ~v0 ~v1 ~v2
  = du_is'45'prop'45'div'45'ℤ_60
du_is'45'prop'45'div'45'ℤ_60 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'div'45'ℤ_60
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'prop'45'map'45'is'45'emb_46
-- elementary-number-theory.divisibility-integers.div-one-ℤ
d_div'45'one'45'ℤ_70 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'one'45'ℤ_70 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) erased
-- elementary-number-theory.divisibility-integers.div-zero-ℤ
d_div'45'zero'45'ℤ_78 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'zero'45'ℤ_78 ~v0 = du_div'45'zero'45'ℤ_78
du_div'45'zero'45'ℤ_78 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'zero'45'ℤ_78
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16)
      erased
-- elementary-number-theory.divisibility-integers.is-zero-div-zero-ℤ
d_is'45'zero'45'div'45'zero'45'ℤ_86 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'div'45'zero'45'ℤ_86 = erased
-- elementary-number-theory.divisibility-integers.div-add-ℤ
d_div'45'add'45'ℤ_100 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'add'45'ℤ_100 ~v0 ~v1 ~v2 v3 v4
  = du_div'45'add'45'ℤ_100 v3 v4
du_div'45'add'45'ℤ_100 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'add'45'ℤ_100 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_add'45'ℤ_4
                       (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.div-neg-ℤ
d_div'45'neg'45'ℤ_134 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'neg'45'ℤ_134 ~v0 ~v1 v2 = du_div'45'neg'45'ℤ_134 v2
du_div'45'neg'45'ℤ_134 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'neg'45'ℤ_134 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.div-int-div-ℕ
d_div'45'int'45'div'45'ℕ_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'int'45'div'45'ℕ_156 ~v0 ~v1 v2
  = du_div'45'int'45'div'45'ℕ_156 v2
du_div'45'int'45'div'45'ℕ_156 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'int'45'div'45'ℕ_156 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.int-abs-is-nonnegative-ℤ
d_int'45'abs'45'is'45'nonnegative'45'ℤ_176 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_int'45'abs'45'is'45'nonnegative'45'ℤ_176 = erased
-- elementary-number-theory.divisibility-integers.div-div-int-ℕ
d_div'45'div'45'int'45'ℕ_184 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'div'45'int'45'ℕ_184 v0
  = case coe v0 of
      0 -> coe
             (\ v1 v2 ->
                seq
                  (coe v2)
                  (coe
                     MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.du_div'45'eq'45'ℕ_504))
      _ -> coe
             (\ v1 v2 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                  (case coe v2 of
                     MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                       -> coe
                            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_abs'45'ℤ_4
                            (coe v3)
                     _ -> MAlonzo.RTE.mazUnreachableError)
                  erased)
-- elementary-number-theory.divisibility-integers.is-unit-ℤ
d_is'45'unit'45'ℤ_208 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'unit'45'ℤ_208 = erased
-- elementary-number-theory.divisibility-integers.unit-ℤ
d_unit'45'ℤ_212 :: ()
d_unit'45'ℤ_212 = erased
-- elementary-number-theory.divisibility-integers.int-unit-ℤ
d_int'45'unit'45'ℤ_214 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_int'45'unit'45'ℤ_214
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- elementary-number-theory.divisibility-integers.is-unit-int-unit-ℤ
d_is'45'unit'45'int'45'unit'45'ℤ_218 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'int'45'unit'45'ℤ_218
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- elementary-number-theory.divisibility-integers.div-is-unit-ℤ
d_div'45'is'45'unit'45'ℤ_224 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'unit'45'ℤ_224 ~v0 v1 v2
  = du_div'45'is'45'unit'45'ℤ_224 v1 v2
du_div'45'is'45'unit'45'ℤ_224 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'unit'45'ℤ_224 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                (coe v0) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.is-one-or-neg-one-ℤ
d_is'45'one'45'or'45'neg'45'one'45'ℤ_242 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'one'45'or'45'neg'45'one'45'ℤ_242 = erased
-- elementary-number-theory.divisibility-integers.is-unit-one-ℤ
d_is'45'unit'45'one'45'ℤ_246 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'one'45'ℤ_246 = coe du_refl'45'div'45'ℤ_14
-- elementary-number-theory.divisibility-integers.one-unit-ℤ
d_one'45'unit'45'ℤ_248 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_one'45'unit'45'ℤ_248
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_one'45'ℤ_30)
      (coe d_is'45'unit'45'one'45'ℤ_246)
-- elementary-number-theory.divisibility-integers.is-unit-is-one-ℤ
d_is'45'unit'45'is'45'one'45'ℤ_252 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'is'45'one'45'ℤ_252 ~v0 ~v1
  = du_is'45'unit'45'is'45'one'45'ℤ_252
du_is'45'unit'45'is'45'one'45'ℤ_252 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'is'45'one'45'ℤ_252
  = coe d_is'45'unit'45'one'45'ℤ_246
-- elementary-number-theory.divisibility-integers.is-unit-neg-one-ℤ
d_is'45'unit'45'neg'45'one'45'ℤ_254 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'neg'45'one'45'ℤ_254
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'one'45'ℤ_10)
      erased
-- elementary-number-theory.divisibility-integers.neg-one-unit-ℤ
d_neg'45'one'45'unit'45'ℤ_256 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_neg'45'one'45'unit'45'ℤ_256
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'one'45'ℤ_10)
      (coe d_is'45'unit'45'neg'45'one'45'ℤ_254)
-- elementary-number-theory.divisibility-integers.is-unit-is-neg-one-ℤ
d_is'45'unit'45'is'45'neg'45'one'45'ℤ_260 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'is'45'neg'45'one'45'ℤ_260 ~v0 ~v1
  = du_is'45'unit'45'is'45'neg'45'one'45'ℤ_260
du_is'45'unit'45'is'45'neg'45'one'45'ℤ_260 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'is'45'neg'45'one'45'ℤ_260
  = coe d_is'45'unit'45'neg'45'one'45'ℤ_254
-- elementary-number-theory.divisibility-integers.is-unit-is-one-or-neg-one-ℤ
d_is'45'unit'45'is'45'one'45'or'45'neg'45'one'45'ℤ_264 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'is'45'one'45'or'45'neg'45'one'45'ℤ_264 ~v0 v1
  = du_is'45'unit'45'is'45'one'45'or'45'neg'45'one'45'ℤ_264 v1
du_is'45'unit'45'is'45'one'45'or'45'neg'45'one'45'ℤ_264 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'is'45'one'45'or'45'neg'45'one'45'ℤ_264 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe du_is'45'unit'45'is'45'one'45'ℤ_252
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe du_is'45'unit'45'is'45'neg'45'one'45'ℤ_260
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.is-one-or-neg-one-is-unit-ℤ
d_is'45'one'45'or'45'neg'45'one'45'is'45'unit'45'ℤ_276 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'one'45'or'45'neg'45'one'45'is'45'unit'45'ℤ_276 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v2 of
             0 -> coe
                    seq (coe v1)
                    (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased)
             _ -> case coe v1 of
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                      -> case coe v3 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> coe
                                  seq (coe v5)
                                  (coe
                                     MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                     erased)
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> case coe v5 of
                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
                                    -> coe
                                         MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                         erased
                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
                                    -> coe
                                         seq (coe v6)
                                         (coe
                                            MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                            erased)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    seq (coe v1)
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                       erased)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    0 -> coe
                           seq (coe v1)
                           (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
                    _ -> case coe v1 of
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                             -> case coe v4 of
                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
                                    -> coe
                                         seq (coe v6)
                                         (coe
                                            MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                            erased)
                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
                                    -> case coe v6 of
                                         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v7
                                           -> coe
                                                MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                                erased
                                         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v7
                                           -> coe
                                                seq (coe v7)
                                                (coe
                                                   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                                                   erased)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.idempotent-is-unit-ℤ
d_idempotent'45'is'45'unit'45'ℤ_340 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_idempotent'45'is'45'unit'45'ℤ_340 = erased
-- elementary-number-theory.divisibility-integers._.f
d_f_350 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_f_350 = erased
-- elementary-number-theory.divisibility-integers.is-one-is-unit-int-ℕ
d_is'45'one'45'is'45'unit'45'int'45'ℕ_354 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'is'45'unit'45'int'45'ℕ_354 = erased
-- elementary-number-theory.divisibility-integers.is-unit-mul-ℤ
d_is'45'unit'45'mul'45'ℤ_380 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'mul'45'ℤ_380 ~v0 ~v1 v2 v3
  = du_is'45'unit'45'mul'45'ℤ_380 v2 v3
du_is'45'unit'45'mul'45'ℤ_380 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'mul'45'ℤ_380 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                       (coe v4) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.mul-unit-ℤ
d_mul'45'unit'45'ℤ_406 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_mul'45'unit'45'ℤ_406 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                       (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe du_is'45'unit'45'mul'45'ℤ_380 (coe v3) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- elementary-number-theory.divisibility-integers.is-unit-left-factor-mul-ℤ
d_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 ~v0 v1 v2
  = du_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 v1 v2
du_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                (coe v2) (coe v0)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.is-unit-right-factor-ℤ
d_is'45'unit'45'right'45'factor'45'ℤ_450 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'right'45'factor'45'ℤ_450 v0 ~v1 v2
  = du_is'45'unit'45'right'45'factor'45'ℤ_450 v0 v2
du_is'45'unit'45'right'45'factor'45'ℤ_450 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'right'45'factor'45'ℤ_450 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             du_is'45'unit'45'left'45'factor'45'mul'45'ℤ_428 (coe v0)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v2) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.presim-unit-ℤ
d_presim'45'unit'45'ℤ_460 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_presim'45'unit'45'ℤ_460 = erased
-- elementary-number-theory.divisibility-integers.sim-unit-ℤ
d_sim'45'unit'45'ℤ_468 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_sim'45'unit'45'ℤ_468 = erased
-- elementary-number-theory.divisibility-integers.sim-unit-presim-unit-ℤ
d_sim'45'unit'45'presim'45'unit'45'ℤ_478 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_sim'45'unit'45'presim'45'unit'45'ℤ_478 ~v0 ~v1 v2 ~v3
  = du_sim'45'unit'45'presim'45'unit'45'ℤ_478 v2
du_sim'45'unit'45'presim'45'unit'45'ℤ_478 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_sim'45'unit'45'presim'45'unit'45'ℤ_478 v0 = coe v0
-- elementary-number-theory.divisibility-integers.presim-unit-sim-unit-ℤ
d_presim'45'unit'45'sim'45'unit'45'ℤ_492 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_presim'45'unit'45'sim'45'unit'45'ℤ_492 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe seq (coe v1) (coe (\ v3 -> coe v3 erased))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe (\ v4 -> coe v4 erased)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v2 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> case coe v3 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> coe
                                  (\ v6 ->
                                     coe
                                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                       (coe d_one'45'unit'45'ℤ_248) erased)
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> coe (\ v6 -> coe v6 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe seq (coe v3) (coe (\ v5 -> coe v5 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.is-nonzero-presim-unit-ℤ
d_is'45'nonzero'45'presim'45'unit'45'ℤ_546 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'presim'45'unit'45'ℤ_546 = erased
-- elementary-number-theory.divisibility-integers._.q
d_q_568 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_q_568 = erased
-- elementary-number-theory.divisibility-integers.is-nonzero-sim-unit-ℤ
d_is'45'nonzero'45'sim'45'unit'45'ℤ_574 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'sim'45'unit'45'ℤ_574 = erased
-- elementary-number-theory.divisibility-integers.is-zero-sim-unit-ℤ
d_is'45'zero'45'sim'45'unit'45'ℤ_584 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'sim'45'unit'45'ℤ_584 = erased
-- elementary-number-theory.divisibility-integers._.K
d_K_598 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_K_598 ~v0 ~v1 v2 ~v3 ~v4 = du_K_598 v2
du_K_598 ::
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_K_598 v0 = coe v0 erased
-- elementary-number-theory.divisibility-integers._.u
d_u_608 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_u_608 ~v0 ~v1 v2 ~v3 ~v4 = du_u_608 v2
du_u_608 ::
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_u_608 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe du_K_598 (coe v0)))
-- elementary-number-theory.divisibility-integers._.β
d_β_618 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_β_618 = erased
-- elementary-number-theory.divisibility-integers.refl-presim-unit-ℤ
d_refl'45'presim'45'unit'45'ℤ_626 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'presim'45'unit'45'ℤ_626 ~v0
  = du_refl'45'presim'45'unit'45'ℤ_626
du_refl'45'presim'45'unit'45'ℤ_626 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'presim'45'unit'45'ℤ_626
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_one'45'unit'45'ℤ_248) erased
-- elementary-number-theory.divisibility-integers.refl-sim-unit-ℤ
d_refl'45'sim'45'unit'45'ℤ_634 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'sim'45'unit'45'ℤ_634 ~v0 ~v1
  = du_refl'45'sim'45'unit'45'ℤ_634
du_refl'45'sim'45'unit'45'ℤ_634 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'sim'45'unit'45'ℤ_634
  = coe du_refl'45'presim'45'unit'45'ℤ_626
-- elementary-number-theory.divisibility-integers.presim-unit-eq-ℤ
d_presim'45'unit'45'eq'45'ℤ_644 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_presim'45'unit'45'eq'45'ℤ_644 ~v0 ~v1 ~v2
  = du_presim'45'unit'45'eq'45'ℤ_644
du_presim'45'unit'45'eq'45'ℤ_644 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_presim'45'unit'45'eq'45'ℤ_644
  = coe du_refl'45'presim'45'unit'45'ℤ_626
-- elementary-number-theory.divisibility-integers.sim-unit-eq-ℤ
d_sim'45'unit'45'eq'45'ℤ_652 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_sim'45'unit'45'eq'45'ℤ_652 ~v0 ~v1 ~v2
  = du_sim'45'unit'45'eq'45'ℤ_652
du_sim'45'unit'45'eq'45'ℤ_652 ::
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_sim'45'unit'45'eq'45'ℤ_652 v0
  = coe du_refl'45'sim'45'unit'45'ℤ_634
-- elementary-number-theory.divisibility-integers.symm-presim-unit-ℤ
d_symm'45'presim'45'unit'45'ℤ_660 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_symm'45'presim'45'unit'45'ℤ_660 ~v0 ~v1 v2
  = du_symm'45'presim'45'unit'45'ℤ_660 v2
du_symm'45'presim'45'unit'45'ℤ_660 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_symm'45'presim'45'unit'45'ℤ_660 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    du_f_676
                    (coe
                       d_is'45'one'45'or'45'neg'45'one'45'is'45'unit'45'ℤ_276 (coe v3)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers._.f
d_f_676 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_f_676 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_f_676 v5
du_f_676 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_f_676 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
           -> coe d_one'45'unit'45'ℤ_248
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
           -> coe d_neg'45'one'45'unit'45'ℤ_256
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.symm-sim-unit-ℤ
d_symm'45'sim'45'unit'45'ℤ_682 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_symm'45'sim'45'unit'45'ℤ_682 ~v0 ~v1 v2 v3
  = du_symm'45'sim'45'unit'45'ℤ_682 v2 v3
du_symm'45'sim'45'unit'45'ℤ_682 ::
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_symm'45'sim'45'unit'45'ℤ_682 v0 v1
  = coe
      du_symm'45'presim'45'unit'45'ℤ_660
      (coe
         v0
         (\ v2 ->
            coe
              v1
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                    (coe v2))
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                    (coe v2)))))
-- elementary-number-theory.divisibility-integers.is-nonzero-sim-unit-ℤ'
d_is'45'nonzero'45'sim'45'unit'45'ℤ''_698 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'sim'45'unit'45'ℤ''_698 = erased
-- elementary-number-theory.divisibility-integers.is-zero-sim-unit-ℤ'
d_is'45'zero'45'sim'45'unit'45'ℤ''_706 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'sim'45'unit'45'ℤ''_706 = erased
-- elementary-number-theory.divisibility-integers.trans-presim-unit-ℤ
d_trans'45'presim'45'unit'45'ℤ_716 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trans'45'presim'45'unit'45'ℤ_716 ~v0 ~v1 ~v2 v3 v4
  = du_trans'45'presim'45'unit'45'ℤ_716 v3 v4
du_trans'45'presim'45'unit'45'ℤ_716 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trans'45'presim'45'unit'45'ℤ_716 v0 v1
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v8 v9
                             -> coe
                                  du_f_740
                                  (coe
                                     d_is'45'one'45'or'45'neg'45'one'45'is'45'unit'45'ℤ_276 (coe v4)
                                     (coe v5))
                                  (coe
                                     d_is'45'one'45'or'45'neg'45'one'45'is'45'unit'45'ℤ_276 (coe v8)
                                     (coe v9))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers._.f
d_f_740 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_f_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_f_740 v9 v10
du_f_740 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_f_740 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
           -> case coe v1 of
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
                  -> coe d_one'45'unit'45'ℤ_248
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
                  -> coe d_neg'45'one'45'unit'45'ℤ_256
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
           -> case coe v1 of
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
                  -> coe d_neg'45'one'45'unit'45'ℤ_256
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
                  -> coe d_one'45'unit'45'ℤ_248
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.trans-sim-unit-ℤ
d_trans'45'sim'45'unit'45'ℤ_748 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trans'45'sim'45'unit'45'ℤ_748 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_trans'45'sim'45'unit'45'ℤ_748 v3 v4
du_trans'45'sim'45'unit'45'ℤ_748 ::
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trans'45'sim'45'unit'45'ℤ_748 v0 v1
  = coe
      du_trans'45'presim'45'unit'45'ℤ_716 (coe v0 erased) (coe v1 erased)
-- elementary-number-theory.divisibility-integers.antisymmetric-div-ℤ
d_antisymmetric'45'div'45'ℤ_778 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_antisymmetric'45'div'45'ℤ_778 v0 ~v1 v2 v3 ~v4
  = du_antisymmetric'45'div'45'ℤ_778 v0 v2 v3
du_antisymmetric'45'div'45'ℤ_778 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_antisymmetric'45'div'45'ℤ_778 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v5 v6
               -> coe
                    du_f_798 (coe v3) erased (coe v5)
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers.d_is'45'decidable'45'is'45'zero'45'ℤ_76
                       (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers._.f
d_f_798 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_f_798 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 = du_f_798 v2 v3 v4 v7
du_f_798 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_f_798 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
        -> coe du_presim'45'unit'45'eq'45'ℤ_644
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v0)
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                   (coe v2) erased))
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.sim-unit-abs-ℤ
d_sim'45'unit'45'abs'45'ℤ_810 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_sim'45'unit'45'abs'45'ℤ_810 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             (\ v2 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                  (coe d_neg'45'one'45'unit'45'ℤ_256) erased)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe seq (coe v1) (\ v2 -> coe du_refl'45'sim'45'unit'45'ℤ_634)
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.divisibility-integers.div-presim-unit-ℤ
d_div'45'presim'45'unit'45'ℤ_830 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'presim'45'unit'45'ℤ_830 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_div'45'presim'45'unit'45'ℤ_830 v4 v5 v6
du_div'45'presim'45'unit'45'ℤ_830 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'presim'45'unit'45'ℤ_830 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v5 v6
                  -> case coe v2 of
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v7 v8
                         -> coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                              (coe
                                 MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
                                 (coe d_int'45'unit'45'ℤ_214 v5) (coe v7))
                              (coe d_int'45'unit'45'ℤ_214 v3)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-integers.div-sim-unit-ℤ
d_div'45'sim'45'unit'45'ℤ_880 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ((MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'sim'45'unit'45'ℤ_880 v0 v1 v2 v3 v4 v5
  = coe
      du_div'45'presim'45'unit'45'ℤ_830
      (coe d_presim'45'unit'45'sim'45'unit'45'ℤ_492 v0 v2 v4)
      (coe d_presim'45'unit'45'sim'45'unit'45'ℤ_492 v1 v3 v5)
-- elementary-number-theory.divisibility-integers.div-int-abs-div-ℤ
d_div'45'int'45'abs'45'div'45'ℤ_898 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'int'45'abs'45'div'45'ℤ_898 v0 v1
  = coe
      d_div'45'sim'45'unit'45'ℤ_880 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_int'45'abs'45'ℤ_10
         v0)
      (coe v1)
      (coe
         du_symm'45'sim'45'unit'45'ℤ_682
         (coe d_sim'45'unit'45'abs'45'ℤ_810 (coe v0)))
      (\ v2 -> coe du_refl'45'sim'45'unit'45'ℤ_634)
-- elementary-number-theory.divisibility-integers.div-div-int-abs-ℤ
d_div'45'div'45'int'45'abs'45'ℤ_908 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'div'45'int'45'abs'45'ℤ_908 v0 v1
  = coe
      d_div'45'sim'45'unit'45'ℤ_880
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_int'45'abs'45'ℤ_10
         v0)
      (coe v1) (coe v0) (coe v1)
      (coe d_sim'45'unit'45'abs'45'ℤ_810 (coe v0))
      (\ v2 -> coe du_refl'45'sim'45'unit'45'ℤ_634)
