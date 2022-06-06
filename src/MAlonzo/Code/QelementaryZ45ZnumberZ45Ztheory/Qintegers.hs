{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qautomorphisms
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- elementary-number-theory.integers.ℤ
d_ℤ_4 :: ()
d_ℤ_4 = erased
-- elementary-number-theory.integers.in-neg
d_in'45'neg_6 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_in'45'neg_6 v0
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0)
-- elementary-number-theory.integers.neg-one-ℤ
d_neg'45'one'45'ℤ_10 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_neg'45'one'45'ℤ_10 = coe d_in'45'neg_6 (coe (0 :: Integer))
-- elementary-number-theory.integers.is-neg-one-ℤ
d_is'45'neg'45'one'45'ℤ_12 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'neg'45'one'45'ℤ_12 = erased
-- elementary-number-theory.integers.zero-ℤ
d_zero'45'ℤ_16 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_zero'45'ℤ_16
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
      (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
-- elementary-number-theory.integers.is-zero-ℤ
d_is'45'zero'45'ℤ_18 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'zero'45'ℤ_18 = erased
-- elementary-number-theory.integers.is-nonzero-ℤ
d_is'45'nonzero'45'ℤ_22 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'nonzero'45'ℤ_22 = erased
-- elementary-number-theory.integers.in-pos
d_in'45'pos_26 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_in'45'pos_26 v0
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
      (coe
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v0))
-- elementary-number-theory.integers.one-ℤ
d_one'45'ℤ_30 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_one'45'ℤ_30 = coe d_in'45'pos_26 (coe (0 :: Integer))
-- elementary-number-theory.integers.is-one-ℤ
d_is'45'one'45'ℤ_32 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'one'45'ℤ_32 = erased
-- elementary-number-theory.integers.int-ℕ
d_int'45'ℕ_36 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_int'45'ℕ_36 v0
  = case coe v0 of
      0 -> coe d_zero'45'ℤ_16
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe d_in'45'pos_26 (coe v1)
-- elementary-number-theory.integers.is-injective-int-ℕ
d_is'45'injective'45'int'45'ℕ_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'int'45'ℕ_40 = erased
-- elementary-number-theory.integers.is-nonzero-int-ℕ
d_is'45'nonzero'45'int'45'ℕ_48 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'int'45'ℕ_48 = erased
-- elementary-number-theory.integers.ind-ℤ
d_ind'45'ℤ_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  AgdaAny ->
  (Integer -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_ind'45'ℤ_64 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_ind'45'ℤ_64 v2 v3 v4 v5 v6 v7
du_ind'45'ℤ_64 ::
  AgdaAny ->
  (Integer -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_ind'45'ℤ_64 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
        -> case coe v6 of
             0 -> coe v0
             _ -> let v7 = subInt (coe v6) (coe (1 :: Integer)) in
                  coe
                    v1 v7
                    (coe
                       du_ind'45'ℤ_64 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v7)))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
        -> case coe v6 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v7 -> coe v2
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v7
               -> case coe v7 of
                    0 -> coe v3
                    _ -> let v8 = subInt (coe v7) (coe (1 :: Integer)) in
                         coe
                           v4 v8
                           (coe
                              du_ind'45'ℤ_64 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                 (coe
                                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                    (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.succ-ℤ
d_succ'45'ℤ_130 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_succ'45'ℤ_130 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> case coe v1 of
             0 -> coe d_zero'45'ℤ_16
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
               -> coe d_one'45'ℤ_30
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                       (coe addInt (coe (1 :: Integer)) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.pred-ℤ
d_pred'45'ℤ_136 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_pred'45'ℤ_136 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe addInt (coe (1 :: Integer)) (coe v1))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe (0 :: Integer))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
               -> case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
                    _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.neg-ℤ
d_neg'45'ℤ_142 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_neg'45'ℤ_142 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.isretr-pred-ℤ
d_isretr'45'pred'45'ℤ_148 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'pred'45'ℤ_148 = erased
-- elementary-number-theory.integers.issec-pred-ℤ
d_issec'45'pred'45'ℤ_154 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'pred'45'ℤ_154 = erased
-- elementary-number-theory.integers.is-equiv-succ-ℤ
d_is'45'equiv'45'succ'45'ℤ_160 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'succ'45'ℤ_160
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_pred'45'ℤ_136) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_pred'45'ℤ_136) erased)
-- elementary-number-theory.integers.equiv-succ-ℤ
d_equiv'45'succ'45'ℤ_162 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'succ'45'ℤ_162
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_succ'45'ℤ_130) (coe d_is'45'equiv'45'succ'45'ℤ_160)
-- elementary-number-theory.integers.is-equiv-pred-ℤ
d_is'45'equiv'45'pred'45'ℤ_164 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pred'45'ℤ_164
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_succ'45'ℤ_130) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_succ'45'ℤ_130) erased)
-- elementary-number-theory.integers.equiv-pred-ℤ
d_equiv'45'pred'45'ℤ_166 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'pred'45'ℤ_166
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_pred'45'ℤ_136) (coe d_is'45'equiv'45'pred'45'ℤ_164)
-- elementary-number-theory.integers.is-injective-succ-ℤ
d_is'45'injective'45'succ'45'ℤ_168 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'succ'45'ℤ_168 = erased
-- elementary-number-theory.integers.has-no-fixed-points-succ-ℤ
d_has'45'no'45'fixed'45'points'45'succ'45'ℤ_178 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_has'45'no'45'fixed'45'points'45'succ'45'ℤ_178 = erased
-- elementary-number-theory.integers.neg-neg-ℤ
d_neg'45'neg'45'ℤ_182 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'neg'45'ℤ_182 = erased
-- elementary-number-theory.integers.is-equiv-neg-ℤ
d_is'45'equiv'45'neg'45'ℤ_188 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'neg'45'ℤ_188
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'ℤ_142) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'ℤ_142) erased)
-- elementary-number-theory.integers.equiv-neg-ℤ
d_equiv'45'neg'45'ℤ_190 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'neg'45'ℤ_190
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_neg'45'ℤ_142) (coe d_is'45'equiv'45'neg'45'ℤ_188)
-- elementary-number-theory.integers.is-emb-neg-ℤ
d_is'45'emb'45'neg'45'ℤ_192 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'neg'45'ℤ_192 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'emb'45'is'45'equiv_878
-- elementary-number-theory.integers.emb-neg-ℤ
d_emb'45'neg'45'ℤ_194 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'neg'45'ℤ_194
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_neg'45'ℤ_142) (coe d_is'45'emb'45'neg'45'ℤ_192)
-- elementary-number-theory.integers.neg-pred-ℤ
d_neg'45'pred'45'ℤ_198 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'pred'45'ℤ_198 = erased
-- elementary-number-theory.integers.neg-succ-ℤ
d_neg'45'succ'45'ℤ_206 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'succ'45'ℤ_206 = erased
-- elementary-number-theory.integers.pred-neg-ℤ
d_pred'45'neg'45'ℤ_214 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_pred'45'neg'45'ℤ_214 = erased
-- elementary-number-theory.integers.is-nonnegative-ℤ
d_is'45'nonnegative'45'ℤ_220 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'nonnegative'45'ℤ_220 = erased
-- elementary-number-theory.integers.is-nonnegative-eq-ℤ
d_is'45'nonnegative'45'eq'45'ℤ_230 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_is'45'nonnegative'45'eq'45'ℤ_230 = erased
-- elementary-number-theory.integers.is-zero-is-nonnegative-ℤ
d_is'45'zero'45'is'45'nonnegative'45'ℤ_234 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'is'45'nonnegative'45'ℤ_234 = erased
-- elementary-number-theory.integers.is-nonnegative-succ-ℤ
d_is'45'nonnegative'45'succ'45'ℤ_242 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_is'45'nonnegative'45'succ'45'ℤ_242 = erased
-- elementary-number-theory.integers.is-positive-ℤ
d_is'45'positive'45'ℤ_250 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'positive'45'ℤ_250 = erased
-- elementary-number-theory.integers.positive-ℤ
d_positive'45'ℤ_258 :: ()
d_positive'45'ℤ_258 = erased
-- elementary-number-theory.integers.is-nonnegative-is-positive-ℤ
d_is'45'nonnegative'45'is'45'positive'45'ℤ_262 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_is'45'nonnegative'45'is'45'positive'45'ℤ_262 = erased
-- elementary-number-theory.integers.is-nonzero-is-positive-ℤ
d_is'45'nonzero'45'is'45'positive'45'ℤ_270 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'is'45'positive'45'ℤ_270 = erased
-- elementary-number-theory.integers.is-positive-eq-ℤ
d_is'45'positive'45'eq'45'ℤ_280 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_is'45'positive'45'eq'45'ℤ_280 = erased
-- elementary-number-theory.integers.is-positive-one-ℤ
d_is'45'positive'45'one'45'ℤ_284 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4
d_is'45'positive'45'one'45'ℤ_284 = erased
-- elementary-number-theory.integers.one-positive-ℤ
d_one'45'positive'45'ℤ_286 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_one'45'positive'45'ℤ_286
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_one'45'ℤ_30) erased
-- elementary-number-theory.integers.is-positive-succ-ℤ
d_is'45'positive'45'succ'45'ℤ_290 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_is'45'positive'45'succ'45'ℤ_290 = erased
-- elementary-number-theory.integers.is-positive-int-ℕ
d_is'45'positive'45'int'45'ℕ_300 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_is'45'positive'45'int'45'ℕ_300 = erased
-- elementary-number-theory.integers.nonnegative-ℤ
d_nonnegative'45'ℤ_308 :: ()
d_nonnegative'45'ℤ_308 = erased
-- elementary-number-theory.integers.int-nonnegative-ℤ
d_int'45'nonnegative'45'ℤ_310 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_int'45'nonnegative'45'ℤ_310
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- elementary-number-theory.integers.is-nonnegative-int-nonnegative-ℤ
d_is'45'nonnegative'45'int'45'nonnegative'45'ℤ_314 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'nonnegative'45'int'45'nonnegative'45'ℤ_314 = erased
-- elementary-number-theory.integers.is-injective-int-nonnegative-ℤ
d_is'45'injective'45'int'45'nonnegative'45'ℤ_316 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'int'45'nonnegative'45'ℤ_316 = erased
-- elementary-number-theory.integers.is-nonnegative-int-ℕ
d_is'45'nonnegative'45'int'45'ℕ_322 :: Integer -> AgdaAny
d_is'45'nonnegative'45'int'45'ℕ_322 = erased
-- elementary-number-theory.integers.nonnegative-int-ℕ
d_nonnegative'45'int'45'ℕ_326 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_nonnegative'45'int'45'ℕ_326 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_int'45'ℕ_36 (coe v0)) erased
-- elementary-number-theory.integers.nat-nonnegative-ℤ
d_nat'45'nonnegative'45'ℤ_332 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
d_nat'45'nonnegative'45'ℤ_332 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe (0 :: Integer)
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe addInt (coe (1 :: Integer)) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.issec-nat-nonnegative-ℤ
d_issec'45'nat'45'nonnegative'45'ℤ_344 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'nat'45'nonnegative'45'ℤ_344 = erased
-- elementary-number-theory.integers.isretr-nat-nonnegative-ℤ
d_isretr'45'nat'45'nonnegative'45'ℤ_350 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'nat'45'nonnegative'45'ℤ_350 = erased
-- elementary-number-theory.integers.is-equiv-nat-nonnegative-ℤ
d_is'45'equiv'45'nat'45'nonnegative'45'ℤ_354 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'nat'45'nonnegative'45'ℤ_354
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_nonnegative'45'int'45'ℕ_326) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_nonnegative'45'int'45'ℕ_326) erased)
-- elementary-number-theory.integers.is-equiv-nonnegative-int-ℕ
d_is'45'equiv'45'nonnegative'45'int'45'ℕ_356 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'nonnegative'45'int'45'ℕ_356
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_nat'45'nonnegative'45'ℤ_332) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_nat'45'nonnegative'45'ℤ_332) erased)
-- elementary-number-theory.integers.equiv-nonnegative-int-ℕ
d_equiv'45'nonnegative'45'int'45'ℕ_358 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'nonnegative'45'int'45'ℕ_358
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_nonnegative'45'int'45'ℕ_326)
      (coe d_is'45'equiv'45'nonnegative'45'int'45'ℕ_356)
-- elementary-number-theory.integers.is-injective-nonnegative-int-ℕ
d_is'45'injective'45'nonnegative'45'int'45'ℕ_360 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'nonnegative'45'int'45'ℕ_360 = erased
-- elementary-number-theory.integers.decide-is-nonnegative-ℤ
d_decide'45'is'45'nonnegative'45'ℤ_370 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_decide'45'is'45'nonnegative'45'ℤ_370 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.succ-int-ℕ
d_succ'45'int'45'ℕ_378 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_succ'45'int'45'ℕ_378 = erased
-- elementary-number-theory.integers.is-injective-neg-ℤ
d_is'45'injective'45'neg'45'ℤ_382 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'neg'45'ℤ_382 = erased
-- elementary-number-theory.integers.is-zero-is-zero-neg-ℤ
d_is'45'zero'45'is'45'zero'45'neg'45'ℤ_392 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'is'45'zero'45'neg'45'ℤ_392 = erased
-- elementary-number-theory.integers.ℤ-Pointed-Type-With-Aut
d_ℤ'45'Pointed'45'Type'45'With'45'Aut_396 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ℤ'45'Pointed'45'Type'45'With'45'Aut_396
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_zero'45'ℤ_16) (coe d_equiv'45'succ'45'ℤ_162))
-- elementary-number-theory.integers.map-ℤ-Pointed-Type-With-Aut
d_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 ~v0 v1 v2
  = du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 v1 v2
du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 v0 v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v2 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.Qautomorphisms.du_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52
                    v0
                    (coe
                       MAlonzo.Code.Qfoundation.Qautomorphisms.du_point'45'Pointed'45'Type'45'With'45'Aut_28
                       (coe v0))
             _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.Qautomorphisms.du_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52
                    v0
                    (coe
                       du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 (coe v0)
                       (coe
                          MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v3)))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.Qautomorphisms.du_point'45'Pointed'45'Type'45'With'45'Aut_28
                    (coe v0)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    0 -> coe
                           MAlonzo.Code.Qfoundation.Qautomorphisms.du_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44
                           v0
                           (coe
                              MAlonzo.Code.Qfoundation.Qautomorphisms.du_point'45'Pointed'45'Type'45'With'45'Aut_28
                              (coe v0))
                    _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.Qfoundation.Qautomorphisms.du_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44
                           v0
                           (coe
                              du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 (coe v0)
                              (coe
                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                 (coe
                                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                    (coe v4))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.integers.preserves-point-map-ℤ-Pointed-Type-With-Aut
d_preserves'45'point'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'point'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_422
  = erased
-- elementary-number-theory.integers.preserves-aut-map-ℤ-Pointed-Type-With-Aut
d_preserves'45'aut'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'aut'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_432
  = erased
-- elementary-number-theory.integers.hom-ℤ-Pointed-Type-With-Aut
d_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 ~v0 v1
  = du_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 v1
du_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_402 (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased erased)
-- elementary-number-theory.integers.htpy-map-ℤ-Pointed-Type-With-Aut
d_htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_462 = erased
-- elementary-number-theory.integers.coh-point-htpy-map-ℤ-Pointed-Type-With-Aut
d_coh'45'point'45'htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'point'45'htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_494
  = erased
-- elementary-number-theory.integers.coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut
d_coh'45'aut'45'htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'aut'45'htpy'45'map'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_508
  = erased
-- elementary-number-theory.integers.htpy-hom-ℤ-Pointed-Type-With-Aut
d_htpy'45'hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_htpy'45'hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_540 ~v0 ~v1
                                                         ~v2
  = du_htpy'45'hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_540
du_htpy'45'hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_540 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_htpy'45'hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_540
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased erased)
-- elementary-number-theory.integers.is-initial-ℤ-Pointed-Type-With-Aut
d_is'45'initial'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'initial'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_550 ~v0 v1
  = du_is'45'initial'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_550 v1
du_is'45'initial'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_550 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'initial'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_550 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_hom'45'ℤ'45'Pointed'45'Type'45'With'45'Aut_452 (coe v0))
      erased
