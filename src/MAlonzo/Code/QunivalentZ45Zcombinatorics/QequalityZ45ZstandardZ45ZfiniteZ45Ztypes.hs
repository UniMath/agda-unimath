{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QsetZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- univalent-combinatorics.equality-standard-finite-types.Eq-Fin
d_Eq'45'Fin_6 :: Integer -> AgdaAny -> AgdaAny -> ()
d_Eq'45'Fin_6 = erased
-- univalent-combinatorics.equality-standard-finite-types.refl-Eq-Fin
d_refl'45'Eq'45'Fin_36 :: Integer -> AgdaAny -> AgdaAny
d_refl'45'Eq'45'Fin_36 = erased
-- univalent-combinatorics.equality-standard-finite-types.Eq-Fin-eq
d_Eq'45'Fin'45'eq_52 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'Fin'45'eq_52 = erased
-- univalent-combinatorics.equality-standard-finite-types.eq-Eq-Fin
d_eq'45'Eq'45'Fin_62 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'Fin_62 = erased
-- univalent-combinatorics.equality-standard-finite-types.is-decidable-Eq-Fin
d_is'45'decidable'45'Eq'45'Fin_80 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'Eq'45'Fin_80 ~v0 v1 v2
  = du_is'45'decidable'45'Eq'45'Fin_80 v1 v2
du_is'45'decidable'45'Eq'45'Fin_80 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'Eq'45'Fin_80 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe du_is'45'decidable'45'Eq'45'Fin_80 (coe v2) (coe v3)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.d_is'45'decidable'45'empty_48
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.d_is'45'decidable'45'empty_48
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.d_is'45'decidable'45'unit_46
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.equality-standard-finite-types.has-decidable-equality-Fin
d_has'45'decidable'45'equality'45'Fin_112 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'Fin_112 ~v0 v1 v2
  = du_has'45'decidable'45'equality'45'Fin_112 v1 v2
du_has'45'decidable'45'equality'45'Fin_112 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'Fin_112 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
      erased erased
      (coe du_is'45'decidable'45'Eq'45'Fin_80 (coe v0) (coe v1))
-- univalent-combinatorics.equality-standard-finite-types.is-decidable-is-zero-Fin
d_is'45'decidable'45'is'45'zero'45'Fin_124 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'zero'45'Fin_124 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      du_has'45'decidable'45'equality'45'Fin_112 (coe v1)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
         (coe v2))
-- univalent-combinatorics.equality-standard-finite-types.is-decidable-is-neg-one-Fin
d_is'45'decidable'45'is'45'neg'45'one'45'Fin_134 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'neg'45'one'45'Fin_134 ~v0 v1
  = du_is'45'decidable'45'is'45'neg'45'one'45'Fin_134 v1
du_is'45'decidable'45'is'45'neg'45'one'45'Fin_134 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'neg'45'one'45'Fin_134 v0
  = coe
      du_has'45'decidable'45'equality'45'Fin_112 (coe v0)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.du_neg'45'one'45'Fin_24)
-- univalent-combinatorics.equality-standard-finite-types.is-decidable-is-one-Fin
d_is'45'decidable'45'is'45'one'45'Fin_144 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'one'45'Fin_144 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      du_has'45'decidable'45'equality'45'Fin_112 (coe v1)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_one'45'Fin_308
         (coe v2))
-- univalent-combinatorics.equality-standard-finite-types.is-set-Fin
d_is'45'set'45'Fin_152 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'Fin_152 v0
  = case coe v0 of
      0 -> \ v1 ->
             coe
               MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'set'45'empty_92
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_is'45'set'45'coprod_378
             (d_is'45'set'45'Fin_152 (coe v1))
             MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'set'45'unit_86
-- univalent-combinatorics.equality-standard-finite-types.Fin-Set
d_Fin'45'Set_158 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Fin'45'Set_158 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'Fin_152 (coe v0))
-- univalent-combinatorics.equality-standard-finite-types.is-prop-is-zero-Fin
d_is'45'prop'45'is'45'zero'45'Fin_168 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'zero'45'Fin_168 v0 v1
  = coe
      d_is'45'set'45'Fin_152 (addInt (coe (1 :: Integer)) (coe v0)) v1
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
         (coe v0))
-- univalent-combinatorics.equality-standard-finite-types.is-prop-is-one-Fin
d_is'45'prop'45'is'45'one'45'Fin_178 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'one'45'Fin_178 v0 v1
  = coe
      d_is'45'set'45'Fin_152 (addInt (coe (1 :: Integer)) (coe v0)) v1
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_one'45'Fin_308
         (coe v0))
-- univalent-combinatorics.equality-standard-finite-types.is-prop-is-zero-or-one-Fin-two-ℕ
d_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186 ~v0
  = du_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186
du_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_is'45'prop'45'coprod_264
-- univalent-combinatorics.equality-standard-finite-types.is-contr-is-zero-or-one-Fin-two-ℕ
d_is'45'contr'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_196 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_196 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
      (coe
         du_is'45'prop'45'is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_186)
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_is'45'zero'45'or'45'one'45'Fin'45'two'45'ℕ_322
         (coe v0))
-- univalent-combinatorics.equality-standard-finite-types.decidable-Eq-Fin
d_decidable'45'Eq'45'Fin_206 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_decidable'45'Eq'45'Fin_206 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_is'45'set'45'Fin_152 v0 v1 v2)
         (coe du_has'45'decidable'45'equality'45'Fin_112 (coe v1) (coe v2)))
-- univalent-combinatorics.equality-standard-finite-types.equiv-unit-trunc-Fin-Set
d_equiv'45'unit'45'trunc'45'Fin'45'Set_228 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'Fin'45'Set_228 v0
  = coe
      MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.d_equiv'45'unit'45'trunc'45'Set_342
      (coe ()) (coe d_Fin'45'Set_158 (coe v0))
