{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.congruence-natural-numbers.cong-ℕ
d_cong'45'ℕ_4 :: Integer -> Integer -> Integer -> ()
d_cong'45'ℕ_4 = erased
-- elementary-number-theory.congruence-natural-numbers._≡_mod_
d__'8801'_mod__12 :: Integer -> Integer -> Integer -> ()
d__'8801'_mod__12 = erased
-- elementary-number-theory.congruence-natural-numbers.concatenate-eq-cong-eq-ℕ
d_concatenate'45'eq'45'cong'45'eq'45'ℕ_30 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'cong'45'eq'45'ℕ_30 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          v6 ~v7
  = du_concatenate'45'eq'45'cong'45'eq'45'ℕ_30 v6
du_concatenate'45'eq'45'cong'45'eq'45'ℕ_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'cong'45'eq'45'ℕ_30 v0 = coe v0
-- elementary-number-theory.congruence-natural-numbers.concatenate-eq-cong-ℕ
d_concatenate'45'eq'45'cong'45'ℕ_44 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'cong'45'ℕ_44 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_concatenate'45'eq'45'cong'45'ℕ_44 v5
du_concatenate'45'eq'45'cong'45'ℕ_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'cong'45'ℕ_44 v0 = coe v0
-- elementary-number-theory.congruence-natural-numbers.concatenate-cong-eq-ℕ
d_concatenate'45'cong'45'eq'45'ℕ_58 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'cong'45'eq'45'ℕ_58 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_concatenate'45'cong'45'eq'45'ℕ_58 v4
du_concatenate'45'cong'45'eq'45'ℕ_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'cong'45'eq'45'ℕ_58 v0 = coe v0
-- elementary-number-theory.congruence-natural-numbers.is-indiscrete-cong-one-ℕ
d_is'45'indiscrete'45'cong'45'one'45'ℕ_68 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'indiscrete'45'cong'45'one'45'ℕ_68 v0 v1
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.d_div'45'one'45'ℕ_94
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
         (coe v0) (coe v1))
-- elementary-number-theory.congruence-natural-numbers.is-discrete-cong-zero-ℕ
d_is'45'discrete'45'cong'45'zero'45'ℕ_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'discrete'45'cong'45'zero'45'ℕ_78 = erased
-- elementary-number-theory.congruence-natural-numbers.cong-zero-ℕ
d_cong'45'zero'45'ℕ_90 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'zero'45'ℕ_90 ~v0 = du_cong'45'zero'45'ℕ_90
du_cong'45'zero'45'ℕ_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'zero'45'ℕ_90
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (1 :: Integer)) erased
-- elementary-number-theory.congruence-natural-numbers.refl-cong-ℕ
d_refl'45'cong'45'ℕ_100 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'cong'45'ℕ_100 ~v0 ~v1 = du_refl'45'cong'45'ℕ_100
du_refl'45'cong'45'ℕ_100 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'cong'45'ℕ_100
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (0 :: Integer)) erased
-- elementary-number-theory.congruence-natural-numbers.cong-identification-ℕ
d_cong'45'identification'45'ℕ_116 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'identification'45'ℕ_116 ~v0 ~v1 ~v2 ~v3
  = du_cong'45'identification'45'ℕ_116
du_cong'45'identification'45'ℕ_116 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'identification'45'ℕ_116 = coe du_refl'45'cong'45'ℕ_100
-- elementary-number-theory.congruence-natural-numbers.symm-cong-ℕ
d_symm'45'cong'45'ℕ_128 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_symm'45'cong'45'ℕ_128 ~v0 ~v1 ~v2 v3
  = du_symm'45'cong'45'ℕ_128 v3
du_symm'45'cong'45'ℕ_128 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_symm'45'cong'45'ℕ_128 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-natural-numbers.cong-zero-ℕ'
d_cong'45'zero'45'ℕ''_152 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'zero'45'ℕ''_152 ~v0 = du_cong'45'zero'45'ℕ''_152
du_cong'45'zero'45'ℕ''_152 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'zero'45'ℕ''_152
  = coe du_symm'45'cong'45'ℕ_128 (coe du_cong'45'zero'45'ℕ_90)
-- elementary-number-theory.congruence-natural-numbers.trans-cong-ℕ
d_trans'45'cong'45'ℕ_164 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trans'45'cong'45'ℕ_164 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_is'45'total'45'dist'45'ℕ_384
              (coe v1) (coe v2) (coe v3) in
    case coe v6 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v7
        -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.du_div'45'add'45'ℕ_142
             (coe v4) (coe v5)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v7
        -> case coe v7 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v8
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.d_div'45'right'45'summand'45'ℕ_226
                    (coe v0)
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
                       (coe v2) (coe v3))
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
                       (coe v1) (coe v3))
                    (coe v5) (coe v4)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v8
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.d_div'45'left'45'summand'45'ℕ_178
                    v0
                    (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
                       (coe v1) (coe v3))
                    (MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
                       (coe v1) (coe v2))
                    v4 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.congruence-natural-numbers.concatenate-cong-eq-cong-ℕ
d_concatenate'45'cong'45'eq'45'cong'45'ℕ_234 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'cong'45'eq'45'cong'45'ℕ_234 v0 v1 v2 ~v3 v4 v5 ~v6
                                             v7
  = du_concatenate'45'cong'45'eq'45'cong'45'ℕ_234 v0 v1 v2 v4 v5 v7
du_concatenate'45'cong'45'eq'45'cong'45'ℕ_234 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'cong'45'eq'45'cong'45'ℕ_234 v0 v1 v2 v3 v4 v5
  = coe
      d_trans'45'cong'45'ℕ_164 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
-- elementary-number-theory.congruence-natural-numbers.concatenate-eq-cong-eq-cong-eq-ℕ
d_concatenate'45'eq'45'cong'45'eq'45'cong'45'eq'45'ℕ_262 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'cong'45'eq'45'cong'45'eq'45'ℕ_262 v0 v1 ~v2
                                                         v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 ~v11
  = du_concatenate'45'eq'45'cong'45'eq'45'cong'45'eq'45'ℕ_262
      v0 v1 v3 v5 v8 v10
du_concatenate'45'eq'45'cong'45'eq'45'cong'45'eq'45'ℕ_262 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'cong'45'eq'45'cong'45'eq'45'ℕ_262 v0 v1 v2
                                                          v3 v4 v5
  = coe
      d_trans'45'cong'45'ℕ_164 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
-- elementary-number-theory.congruence-natural-numbers.eq-cong-le-dist-ℕ
d_eq'45'cong'45'le'45'dist'45'ℕ_282 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cong'45'le'45'dist'45'ℕ_282 = erased
-- elementary-number-theory.congruence-natural-numbers.eq-cong-le-ℕ
d_eq'45'cong'45'le'45'ℕ_300 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cong'45'le'45'ℕ_300 = erased
-- elementary-number-theory.congruence-natural-numbers.eq-cong-nat-Fin
d_eq'45'cong'45'nat'45'Fin_318 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cong'45'nat'45'Fin_318 = erased
-- elementary-number-theory.congruence-natural-numbers.cong-is-zero-nat-zero-Fin
d_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330 ~v0
  = du_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330
du_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330
  = coe du_cong'45'identification'45'ℕ_116
-- elementary-number-theory.congruence-natural-numbers.eq-cong-zero-ℕ
d_eq'45'cong'45'zero'45'ℕ_338 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cong'45'zero'45'ℕ_338 = erased
-- elementary-number-theory.congruence-natural-numbers.is-one-cong-succ-ℕ
d_is'45'one'45'cong'45'succ'45'ℕ_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'cong'45'succ'45'ℕ_350 = erased
-- elementary-number-theory.congruence-natural-numbers.scalar-invariant-cong-ℕ
d_scalar'45'invariant'45'cong'45'ℕ_366 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_scalar'45'invariant'45'cong'45'ℕ_366 ~v0 ~v1 ~v2 v3 v4
  = du_scalar'45'invariant'45'cong'45'ℕ_366 v3 v4
du_scalar'45'invariant'45'cong'45'ℕ_366 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_scalar'45'invariant'45'cong'45'ℕ_366 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                (coe v0) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-natural-numbers.scalar-invariant-cong-ℕ'
d_scalar'45'invariant'45'cong'45'ℕ''_400 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_scalar'45'invariant'45'cong'45'ℕ''_400 ~v0 ~v1 ~v2 v3 v4
  = du_scalar'45'invariant'45'cong'45'ℕ''_400 v3 v4
du_scalar'45'invariant'45'cong'45'ℕ''_400 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_scalar'45'invariant'45'cong'45'ℕ''_400 v0 v1
  = coe du_scalar'45'invariant'45'cong'45'ℕ_366 (coe v0) (coe v1)
-- elementary-number-theory.congruence-natural-numbers.congruence-mul-ℕ
d_congruence'45'mul'45'ℕ_422 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_congruence'45'mul'45'ℕ_422 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_trans'45'cong'45'ℕ_164 (coe v0)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
         (coe v1) (coe v4))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
         (coe v3) (coe v4))
      (coe du_scalar'45'invariant'45'cong'45'ℕ_366 (coe v1) (coe v6))
      (coe du_scalar'45'invariant'45'cong'45'ℕ''_400 (coe v4) (coe v5))
-- elementary-number-theory.congruence-natural-numbers.translation-invariant-cong-ℕ
d_translation'45'invariant'45'cong'45'ℕ_446 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_translation'45'invariant'45'cong'45'ℕ_446 ~v0 ~v1 ~v2 ~v3 v4
  = du_translation'45'invariant'45'cong'45'ℕ_446 v4
du_translation'45'invariant'45'cong'45'ℕ_446 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_translation'45'invariant'45'cong'45'ℕ_446 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-natural-numbers.translation-invariant-cong-ℕ'
d_translation'45'invariant'45'cong'45'ℕ''_480 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_translation'45'invariant'45'cong'45'ℕ''_480 ~v0 ~v1 ~v2 ~v3 v4
  = du_translation'45'invariant'45'cong'45'ℕ''_480 v4
du_translation'45'invariant'45'cong'45'ℕ''_480 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_translation'45'invariant'45'cong'45'ℕ''_480 v0
  = coe du_translation'45'invariant'45'cong'45'ℕ_446 (coe v0)
-- elementary-number-theory.congruence-natural-numbers.step-invariant-cong-ℕ
d_step'45'invariant'45'cong'45'ℕ_498 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_step'45'invariant'45'cong'45'ℕ_498 ~v0 ~v1 ~v2
  = du_step'45'invariant'45'cong'45'ℕ_498
du_step'45'invariant'45'cong'45'ℕ_498 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_step'45'invariant'45'cong'45'ℕ_498
  = coe du_translation'45'invariant'45'cong'45'ℕ''_480
-- elementary-number-theory.congruence-natural-numbers.reflects-cong-add-ℕ
d_reflects'45'cong'45'add'45'ℕ_514 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reflects'45'cong'45'add'45'ℕ_514 ~v0 ~v1 ~v2 ~v3 v4
  = du_reflects'45'cong'45'add'45'ℕ_514 v4
du_reflects'45'cong'45'add'45'ℕ_514 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reflects'45'cong'45'add'45'ℕ_514 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.congruence-natural-numbers.reflects-cong-add-ℕ'
d_reflects'45'cong'45'add'45'ℕ''_548 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reflects'45'cong'45'add'45'ℕ''_548 ~v0 ~v1 ~v2 ~v3 v4
  = du_reflects'45'cong'45'add'45'ℕ''_548 v4
du_reflects'45'cong'45'add'45'ℕ''_548 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reflects'45'cong'45'add'45'ℕ''_548 v0
  = coe du_reflects'45'cong'45'add'45'ℕ_514 (coe v0)
