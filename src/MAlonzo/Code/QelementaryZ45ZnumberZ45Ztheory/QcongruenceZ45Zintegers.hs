{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.congruence-integers.cong-ℤ
d_cong'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_cong'45'ℤ_4 = erased
-- elementary-number-theory.congruence-integers.is-cong-zero-ℤ
d_is'45'cong'45'zero'45'ℤ_12 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'cong'45'zero'45'ℤ_12 = erased
-- elementary-number-theory.congruence-integers.is-cong-zero-div-ℤ
d_is'45'cong'45'zero'45'div'45'ℤ_22 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'cong'45'zero'45'div'45'ℤ_22 ~v0 ~v1 v2
  = du_is'45'cong'45'zero'45'div'45'ℤ_22 v2
du_is'45'cong'45'zero'45'div'45'ℤ_22 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'cong'45'zero'45'div'45'ℤ_22 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.div-is-cong-zero-ℤ
d_div'45'is'45'cong'45'zero'45'ℤ_44 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'cong'45'zero'45'ℤ_44 ~v0 ~v1 v2
  = du_div'45'is'45'cong'45'zero'45'ℤ_44 v2
du_div'45'is'45'cong'45'zero'45'ℤ_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'cong'45'zero'45'ℤ_44 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.is-indiscrete-cong-ℤ
d_is'45'indiscrete'45'cong'45'ℤ_68 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'indiscrete'45'cong'45'ℤ_68 ~v0 v1 v2 v3
  = du_is'45'indiscrete'45'cong'45'ℤ_68 v1 v2 v3
du_is'45'indiscrete'45'cong'45'ℤ_68 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'indiscrete'45'cong'45'ℤ_68 v0 v1 v2
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_div'45'is'45'unit'45'ℤ_224
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
         (coe v1) (coe v2))
      (coe v0)
-- elementary-number-theory.congruence-integers.is-discrete-cong-ℤ
d_is'45'discrete'45'cong'45'ℤ_84 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'discrete'45'cong'45'ℤ_84 = erased
-- elementary-number-theory.congruence-integers.is-unit-cong-succ-ℤ
d_is'45'unit'45'cong'45'succ'45'ℤ_96 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'cong'45'succ'45'ℤ_96 ~v0 ~v1 v2
  = du_is'45'unit'45'cong'45'succ'45'ℤ_96 v2
du_is'45'unit'45'cong'45'succ'45'ℤ_96 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'cong'45'succ'45'ℤ_96 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.is-unit-cong-pred-ℤ
d_is'45'unit'45'cong'45'pred'45'ℤ_118 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'unit'45'cong'45'pred'45'ℤ_118 ~v0 ~v1 v2
  = du_is'45'unit'45'cong'45'pred'45'ℤ_118 v2
du_is'45'unit'45'cong'45'pred'45'ℤ_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'unit'45'cong'45'pred'45'ℤ_118 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.refl-cong-ℤ
d_refl'45'cong'45'ℤ_140 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'cong'45'ℤ_140 ~v0 ~v1 = du_refl'45'cong'45'ℤ_140
du_refl'45'cong'45'ℤ_140 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'cong'45'ℤ_140
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16)
      erased
-- elementary-number-theory.congruence-integers.symmetric-cong-ℤ
d_symmetric'45'cong'45'ℤ_156 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_symmetric'45'cong'45'ℤ_156 ~v0 ~v1 ~v2 v3
  = du_symmetric'45'cong'45'ℤ_156 v3
du_symmetric'45'cong'45'ℤ_156 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_symmetric'45'cong'45'ℤ_156 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.transitive-cong-ℤ
d_transitive'45'cong'45'ℤ_186 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_transitive'45'cong'45'ℤ_186 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_transitive'45'cong'45'ℤ_186 v4 v5
du_transitive'45'cong'45'ℤ_186 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_transitive'45'cong'45'ℤ_186 v0 v1
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
-- elementary-number-theory.congruence-integers.concatenate-eq-cong-ℤ
d_concatenate'45'eq'45'cong'45'ℤ_228 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'cong'45'ℤ_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_concatenate'45'eq'45'cong'45'ℤ_228 v5
du_concatenate'45'eq'45'cong'45'ℤ_228 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'cong'45'ℤ_228 v0 = coe v0
-- elementary-number-theory.congruence-integers.concatenate-cong-eq-ℤ
d_concatenate'45'cong'45'eq'45'ℤ_244 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'cong'45'eq'45'ℤ_244 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_concatenate'45'cong'45'eq'45'ℤ_244 v4
du_concatenate'45'cong'45'eq'45'ℤ_244 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'cong'45'eq'45'ℤ_244 v0 = coe v0
-- elementary-number-theory.congruence-integers.concatenate-eq-cong-eq-ℤ
d_concatenate'45'eq'45'cong'45'eq'45'ℤ_264 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'cong'45'eq'45'ℤ_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           v6 ~v7
  = du_concatenate'45'eq'45'cong'45'eq'45'ℤ_264 v6
du_concatenate'45'eq'45'cong'45'eq'45'ℤ_264 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'cong'45'eq'45'ℤ_264 v0 = coe v0
-- elementary-number-theory.congruence-integers.concatenate-cong-eq-cong-ℤ
d_concatenate'45'cong'45'eq'45'cong'45'ℤ_284 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'cong'45'eq'45'cong'45'ℤ_284 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                             ~v6 v7
  = du_concatenate'45'cong'45'eq'45'cong'45'ℤ_284 v5 v7
du_concatenate'45'cong'45'eq'45'cong'45'ℤ_284 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'cong'45'eq'45'cong'45'ℤ_284 v0 v1
  = coe du_transitive'45'cong'45'ℤ_186 (coe v0) (coe v1)
-- elementary-number-theory.congruence-integers.concatenate-cong-cong-cong-ℤ
d_concatenate'45'cong'45'cong'45'cong'45'ℤ_308 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'cong'45'cong'45'cong'45'ℤ_308 ~v0 ~v1 ~v2 ~v3 ~v4
                                               v5 v6 v7
  = du_concatenate'45'cong'45'cong'45'cong'45'ℤ_308 v5 v6 v7
du_concatenate'45'cong'45'cong'45'cong'45'ℤ_308 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'cong'45'cong'45'cong'45'ℤ_308 v0 v1 v2
  = coe
      du_transitive'45'cong'45'ℤ_186 (coe v0)
      (coe du_transitive'45'cong'45'ℤ_186 (coe v1) (coe v2))
-- elementary-number-theory.congruence-integers.cong-cong-neg-ℤ
d_cong'45'cong'45'neg'45'ℤ_332 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'cong'45'neg'45'ℤ_332 ~v0 ~v1 ~v2 v3
  = du_cong'45'cong'45'neg'45'ℤ_332 v3
du_cong'45'cong'45'neg'45'ℤ_332 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'cong'45'neg'45'ℤ_332 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.cong-neg-cong-ℤ
d_cong'45'neg'45'cong'45'ℤ_360 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'neg'45'cong'45'ℤ_360 ~v0 ~v1 ~v2 v3
  = du_cong'45'neg'45'cong'45'ℤ_360 v3
du_cong'45'neg'45'cong'45'ℤ_360 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'neg'45'cong'45'ℤ_360 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
                (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-integers.cong-int-cong-ℕ
d_cong'45'int'45'cong'45'ℕ_388 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'int'45'cong'45'ℕ_388 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.d_div'45'sim'45'unit'45'ℤ_880
      (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
         (coe v0))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_int'45'abs'45'ℤ_10
         (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v1))
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v2))))
      (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
         (coe v0))
      (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
            (coe v1))
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
            (coe v2)))
      (\ v4 ->
         coe
           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_refl'45'sim'45'unit'45'ℤ_634)
      (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.d_sim'45'unit'45'abs'45'ℤ_810
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v1))
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v2))))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_div'45'int'45'div'45'ℕ_156
         (coe v3))
-- elementary-number-theory.congruence-integers.cong-cong-int-ℕ
d_cong'45'cong'45'int'45'ℕ_404 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'cong'45'int'45'ℕ_404 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.d_div'45'div'45'int'45'ℕ_184
      v0
      (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.d_div'45'sim'45'unit'45'ℤ_880
         (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
            (coe v0))
         (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v1))
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
               (coe v2)))
         (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
            (coe v0))
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QabsoluteZ45ZvalueZ45Zintegers.d_int'45'abs'45'ℤ_10
            (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
               (coe
                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                  (coe v1))
               (coe
                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                  (coe v2))))
         (\ v4 ->
            coe
              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_refl'45'sim'45'unit'45'ℤ_634)
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_symm'45'sim'45'unit'45'ℤ_682
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.d_sim'45'unit'45'abs'45'ℤ_810
               (coe
                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
                  (coe
                     MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                     (coe v1))
                  (coe
                     MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
                     (coe v2)))))
         v3)
