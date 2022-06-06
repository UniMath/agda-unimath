{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qbooleans
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- univalent-combinatorics.standard-finite-types.Fin
d_Fin_4 :: Integer -> ()
d_Fin_4 = erased
-- univalent-combinatorics.standard-finite-types.inl-Fin
d_inl'45'Fin_10 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_inl'45'Fin_10 ~v0 = du_inl'45'Fin_10
du_inl'45'Fin_10 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_inl'45'Fin_10
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
-- univalent-combinatorics.standard-finite-types.emb-inl-Fin
d_emb'45'inl'45'Fin_16 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'inl'45'Fin_16 ~v0 = du_emb'45'inl'45'Fin_16
du_emb'45'inl'45'Fin_16 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'inl'45'Fin_16
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_inl'45'Fin_10)
      (coe
         MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_is'45'emb'45'inl_222)
-- univalent-combinatorics.standard-finite-types.neg-one-Fin
d_neg'45'one'45'Fin_24 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_neg'45'one'45'Fin_24 ~v0 = du_neg'45'one'45'Fin_24
du_neg'45'one'45'Fin_24 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_neg'45'one'45'Fin_24
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
-- univalent-combinatorics.standard-finite-types.is-neg-one-Fin
d_is'45'neg'45'one'45'Fin_30 :: Integer -> AgdaAny -> ()
d_is'45'neg'45'one'45'Fin_30 = erased
-- univalent-combinatorics.standard-finite-types.neg-two-Fin
d_neg'45'two'45'Fin_38 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_neg'45'two'45'Fin_38 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      _ -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased)
-- univalent-combinatorics.standard-finite-types.is-inl-Fin
d_is'45'inl'45'Fin_44 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_is'45'inl'45'Fin_44 = erased
-- univalent-combinatorics.standard-finite-types.is-neg-one-is-not-inl-Fin
d_is'45'neg'45'one'45'is'45'not'45'inl'45'Fin_56 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'neg'45'one'45'is'45'not'45'inl'45'Fin_56 = erased
-- univalent-combinatorics.standard-finite-types.raise-Fin
d_raise'45'Fin_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> Integer -> ()
d_raise'45'Fin_68 = erased
-- univalent-combinatorics.standard-finite-types.equiv-raise-Fin
d_equiv'45'raise'45'Fin_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'raise'45'Fin_78 ~v0 ~v1 = du_equiv'45'raise'45'Fin_78
du_equiv'45'raise'45'Fin_78 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'raise'45'Fin_78
  = coe
      MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50
-- univalent-combinatorics.standard-finite-types.map-raise-Fin
d_map'45'raise'45'Fin_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10
d_map'45'raise'45'Fin_88 ~v0 ~v1 = du_map'45'raise'45'Fin_88
du_map'45'raise'45'Fin_88 ::
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10
du_map'45'raise'45'Fin_88
  = coe
      MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.C_map'45'raise_18
-- univalent-combinatorics.standard-finite-types.is-decidable-is-inl-Fin
d_is'45'decidable'45'is'45'inl'45'Fin_98 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'inl'45'Fin_98 ~v0 v1
  = du_is'45'decidable'45'is'45'inl'45'Fin_98 v1
du_is'45'decidable'45'is'45'inl'45'Fin_98 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'inl'45'Fin_98 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v1) erased)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types._.α
d_α_106 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_α_106 = erased
-- univalent-combinatorics.standard-finite-types.map-equiv-Fin-one-ℕ
d_map'45'equiv'45'Fin'45'one'45'ℕ_110 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4
d_map'45'equiv'45'Fin'45'one'45'ℕ_110 = erased
-- univalent-combinatorics.standard-finite-types.inv-map-equiv-Fin-one-ℕ
d_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112 ~v0
  = du_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112
du_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
-- univalent-combinatorics.standard-finite-types.issec-inv-map-equiv-Fin-one-ℕ
d_issec'45'inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_114 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_114 = erased
-- univalent-combinatorics.standard-finite-types.isretr-inv-map-equiv-Fin-one-ℕ
d_isretr'45'inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_116 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_116 = erased
-- univalent-combinatorics.standard-finite-types.is-equiv-map-equiv-Fin-one-ℕ
d_is'45'equiv'45'map'45'equiv'45'Fin'45'one'45'ℕ_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'equiv'45'Fin'45'one'45'ℕ_118
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe du_inv'45'map'45'equiv'45'Fin'45'one'45'ℕ_112) erased
      erased
-- univalent-combinatorics.standard-finite-types.equiv-Fin-one-ℕ
d_equiv'45'Fin'45'one'45'ℕ_120 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Fin'45'one'45'ℕ_120
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'equiv'45'map'45'equiv'45'Fin'45'one'45'ℕ_118)
-- univalent-combinatorics.standard-finite-types.is-contr-Fin-one-ℕ
d_is'45'contr'45'Fin'45'one'45'ℕ_122 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'Fin'45'one'45'ℕ_122
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
      (coe d_equiv'45'Fin'45'one'45'ℕ_120)
      (coe
         MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'contr'45'unit_42)
-- univalent-combinatorics.standard-finite-types.is-not-contractible-Fin
d_is'45'not'45'contractible'45'Fin_126 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'contractible'45'Fin_126 = erased
-- univalent-combinatorics.standard-finite-types.bool-Fin-two-ℕ
d_bool'45'Fin'45'two'45'ℕ_140 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Bool
d_bool'45'Fin'45'two'45'ℕ_140 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Qfoundation.Qbooleans.C_true_6)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.Qbooleans.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.Fin-two-ℕ-bool
d_Fin'45'two'45'ℕ'45'bool_142 ::
  Bool -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_Fin'45'two'45'ℕ'45'bool_142 v0
  = if coe v0
      then coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased)
      else coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
-- univalent-combinatorics.standard-finite-types.isretr-Fin-two-ℕ-bool
d_isretr'45'Fin'45'two'45'ℕ'45'bool_144 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'Fin'45'two'45'ℕ'45'bool_144 = erased
-- univalent-combinatorics.standard-finite-types.issec-Fin-two-ℕ-bool
d_issec'45'Fin'45'two'45'ℕ'45'bool_146 ::
  Bool -> MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'Fin'45'two'45'ℕ'45'bool_146 = erased
-- univalent-combinatorics.standard-finite-types.equiv-bool-Fin-two-ℕ
d_equiv'45'bool'45'Fin'45'two'45'ℕ_148 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'bool'45'Fin'45'two'45'ℕ_148
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_bool'45'Fin'45'two'45'ℕ_140)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe d_Fin'45'two'45'ℕ'45'bool_142) erased erased)
-- univalent-combinatorics.standard-finite-types.nat-Fin
d_nat'45'Fin_152 :: Integer -> AgdaAny -> Integer
d_nat'45'Fin_152 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
        -> coe d_nat'45'Fin_152 (coe v2) (coe v3)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.strict-upper-bound-nat-Fin
d_strict'45'upper'45'bound'45'nat'45'Fin_166 ::
  Integer -> AgdaAny -> AgdaAny
d_strict'45'upper'45'bound'45'nat'45'Fin_166 = erased
-- univalent-combinatorics.standard-finite-types.upper-bound-nat-Fin
d_upper'45'bound'45'nat'45'Fin_178 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_upper'45'bound'45'nat'45'Fin_178 = erased
-- univalent-combinatorics.standard-finite-types.is-injective-nat-Fin
d_is'45'injective'45'nat'45'Fin_188 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'nat'45'Fin_188 = erased
-- univalent-combinatorics.standard-finite-types.is-emb-nat-Fin
d_is'45'emb'45'nat'45'Fin_216 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'nat'45'Fin_216 ~v0 = du_is'45'emb'45'nat'45'Fin_216
du_is'45'emb'45'nat'45'Fin_216 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'nat'45'Fin_216
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- univalent-combinatorics.standard-finite-types.emb-nat-Fin
d_emb'45'nat'45'Fin_222 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'nat'45'Fin_222 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_nat'45'Fin_152 (coe v0))
      (coe du_is'45'emb'45'nat'45'Fin_216)
-- univalent-combinatorics.standard-finite-types.zero-Fin
d_zero'45'Fin_230 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_zero'45'Fin_230 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe d_zero'45'Fin_230 (coe v1))
-- univalent-combinatorics.standard-finite-types.is-zero-Fin
d_is'45'zero'45'Fin_236 :: Integer -> AgdaAny -> ()
d_is'45'zero'45'Fin_236 = erased
-- univalent-combinatorics.standard-finite-types.is-zero-Fin'
d_is'45'zero'45'Fin''_244 :: Integer -> AgdaAny -> ()
d_is'45'zero'45'Fin''_244 = erased
-- univalent-combinatorics.standard-finite-types.is-nonzero-Fin
d_is'45'nonzero'45'Fin_252 :: Integer -> AgdaAny -> ()
d_is'45'nonzero'45'Fin_252 = erased
-- univalent-combinatorics.standard-finite-types.skip-zero-Fin
d_skip'45'zero'45'Fin_260 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_skip'45'zero'45'Fin_260 ~v0 v1 = du_skip'45'zero'45'Fin_260 v1
du_skip'45'zero'45'Fin_260 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_skip'45'zero'45'Fin_260 v0 = coe v0
-- univalent-combinatorics.standard-finite-types.succ-Fin
d_succ'45'Fin_270 :: Integer -> AgdaAny -> AgdaAny
d_succ'45'Fin_270 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3 -> coe v3
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
        -> coe d_zero'45'Fin_230 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.is-zero-nat-zero-Fin
d_is'45'zero'45'nat'45'zero'45'Fin_280 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'nat'45'zero'45'Fin_280 = erased
-- univalent-combinatorics.standard-finite-types.nat-skip-zero-Fin
d_nat'45'skip'45'zero'45'Fin_288 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_nat'45'skip'45'zero'45'Fin_288 = erased
-- univalent-combinatorics.standard-finite-types.nat-succ-Fin
d_nat'45'succ'45'Fin_300 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_nat'45'succ'45'Fin_300 = erased
-- univalent-combinatorics.standard-finite-types.one-Fin
d_one'45'Fin_308 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_one'45'Fin_308 v0
  = coe
      d_succ'45'Fin_270 (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe d_zero'45'Fin_230 (coe v0))
-- univalent-combinatorics.standard-finite-types.is-one-Fin
d_is'45'one'45'Fin_314 :: Integer -> AgdaAny -> ()
d_is'45'one'45'Fin_314 = erased
-- univalent-combinatorics.standard-finite-types.is-zero-or-one-Fin-two-ℕ
d_is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_322 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_322 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.is-one-nat-one-Fin
d_is'45'one'45'nat'45'one'45'Fin_326 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'nat'45'one'45'Fin_326 = erased
-- univalent-combinatorics.standard-finite-types.is-injective-inl-Fin
d_is'45'injective'45'inl'45'Fin_332 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'inl'45'Fin_332 = erased
-- univalent-combinatorics.standard-finite-types.neq-zero-succ-Fin
d_neq'45'zero'45'succ'45'Fin_338 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'zero'45'succ'45'Fin_338 = erased
-- univalent-combinatorics.standard-finite-types.is-injective-skip-zero-Fin
d_is'45'injective'45'skip'45'zero'45'Fin_350 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'skip'45'zero'45'Fin_350 = erased
-- univalent-combinatorics.standard-finite-types.is-injective-succ-Fin
d_is'45'injective'45'succ'45'Fin_374 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'succ'45'Fin_374 = erased
-- univalent-combinatorics.standard-finite-types.skip-neg-two-Fin
d_skip'45'neg'45'two'45'Fin_402 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_skip'45'neg'45'two'45'Fin_402 ~v0 v1
  = du_skip'45'neg'45'two'45'Fin_402 v1
du_skip'45'neg'45'two'45'Fin_402 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_skip'45'neg'45'two'45'Fin_402 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe du_neg'45'one'45'Fin_24
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.pred-Fin
d_pred'45'Fin_414 :: Integer -> AgdaAny -> AgdaAny
d_pred'45'Fin_414 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
        -> coe
             du_skip'45'neg'45'two'45'Fin_402
             (coe d_pred'45'Fin_414 (coe v2) (coe v3))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
        -> coe d_neg'45'two'45'Fin_38 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.standard-finite-types.pred-zero-Fin
d_pred'45'zero'45'Fin_426 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_pred'45'zero'45'Fin_426 = erased
-- univalent-combinatorics.standard-finite-types.succ-skip-neg-two-Fin
d_succ'45'skip'45'neg'45'two'45'Fin_434 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_succ'45'skip'45'neg'45'two'45'Fin_434 = erased
-- univalent-combinatorics.standard-finite-types.issec-pred-Fin
d_issec'45'pred'45'Fin_446 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'pred'45'Fin_446 = erased
-- univalent-combinatorics.standard-finite-types.isretr-pred-Fin
d_isretr'45'pred'45'Fin_458 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'pred'45'Fin_458 = erased
-- univalent-combinatorics.standard-finite-types.is-equiv-succ-Fin
d_is'45'equiv'45'succ'45'Fin_470 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'succ'45'Fin_470 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_pred'45'Fin_414 (coe v0)) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_pred'45'Fin_414 (coe v0)) erased)
-- univalent-combinatorics.standard-finite-types.equiv-succ-Fin
d_equiv'45'succ'45'Fin_474 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'succ'45'Fin_474 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_succ'45'Fin_270 (coe v0))
      (coe d_is'45'equiv'45'succ'45'Fin_470 (coe v0))
-- univalent-combinatorics.standard-finite-types.is-equiv-pred-Fin
d_is'45'equiv'45'pred'45'Fin_478 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pred'45'Fin_478 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_succ'45'Fin_270 (coe v0)) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_succ'45'Fin_270 (coe v0)) erased)
-- univalent-combinatorics.standard-finite-types.equiv-pred-Fin
d_equiv'45'pred'45'Fin_482 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'pred'45'Fin_482 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_pred'45'Fin_414 (coe v0))
      (coe d_is'45'equiv'45'pred'45'Fin_478 (coe v0))
-- univalent-combinatorics.standard-finite-types.leq-nat-succ-Fin
d_leq'45'nat'45'succ'45'Fin_488 :: Integer -> AgdaAny -> AgdaAny
d_leq'45'nat'45'succ'45'Fin_488 = erased
-- univalent-combinatorics.standard-finite-types.is-injective-Fin
d_is'45'injective'45'Fin_500 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'Fin_500 = erased
