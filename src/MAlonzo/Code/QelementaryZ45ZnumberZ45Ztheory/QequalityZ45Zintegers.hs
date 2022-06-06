{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QsetZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- elementary-number-theory.equality-integers.Eq-ℤ
d_Eq'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_Eq'45'ℤ_4 = erased
-- elementary-number-theory.equality-integers.refl-Eq-ℤ
d_refl'45'Eq'45'ℤ_36 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_refl'45'Eq'45'ℤ_36 = erased
-- elementary-number-theory.equality-integers.Eq-eq-ℤ
d_Eq'45'eq'45'ℤ_48 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'eq'45'ℤ_48 = erased
-- elementary-number-theory.equality-integers.eq-Eq-ℤ
d_eq'45'Eq'45'ℤ_56 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'ℤ_56 = erased
-- elementary-number-theory.equality-integers.has-decidable-equality-ℤ
d_has'45'decidable'45'equality'45'ℤ_72 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'ℤ_72
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'coprod_594
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_has'45'decidable'45'equality'45'ℕ_74)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'coprod_594
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'unit_30)
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_has'45'decidable'45'equality'45'ℕ_74))
-- elementary-number-theory.equality-integers.is-decidable-is-zero-ℤ
d_is'45'decidable'45'is'45'zero'45'ℤ_76 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'zero'45'ℤ_76 v0
  = coe
      d_has'45'decidable'45'equality'45'ℤ_72 v0
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
-- elementary-number-theory.equality-integers.is-decidable-is-one-ℤ
d_is'45'decidable'45'is'45'one'45'ℤ_82 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'one'45'ℤ_82 v0
  = coe
      d_has'45'decidable'45'equality'45'ℤ_72 v0
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_one'45'ℤ_30
-- elementary-number-theory.equality-integers.is-decidable-is-neg-one-ℤ
d_is'45'decidable'45'is'45'neg'45'one'45'ℤ_88 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'neg'45'one'45'ℤ_88 v0
  = coe
      d_has'45'decidable'45'equality'45'ℤ_72 v0
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'one'45'ℤ_10
-- elementary-number-theory.equality-integers.is-set-ℤ
d_is'45'set'45'ℤ_92 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'ℤ_92
  = coe
      MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_is'45'set'45'coprod_378
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_is'45'set'45'ℕ_56
      (coe
         MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_is'45'set'45'coprod_378
         MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'set'45'unit_86
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_is'45'set'45'ℕ_56)
-- elementary-number-theory.equality-integers.ℤ-Set
d_ℤ'45'Set_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ℤ'45'Set_94
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'ℤ_92)
-- elementary-number-theory.equality-integers.equiv-unit-trunc-ℤ-Set
d_equiv'45'unit'45'trunc'45'ℤ'45'Set_96 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'ℤ'45'Set_96
  = coe
      MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.d_equiv'45'unit'45'trunc'45'Set_342
      (coe ()) (coe d_ℤ'45'Set_94)
-- elementary-number-theory.equality-integers.is-prop-Eq-ℤ
d_is'45'prop'45'Eq'45'ℤ_102 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Eq'45'ℤ_102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_is'45'prop'45'Eq'45'ℕ_18
                    (coe v2) (coe v3)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> \ v4 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> \ v4 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v2 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> case coe v3 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> coe
                                  MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> \ v6 ->
                                  coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> case coe v3 of
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                             -> \ v6 ->
                                  coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                             -> coe
                                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_is'45'prop'45'Eq'45'ℕ_18
                                  (coe v4) (coe v5)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.equality-integers.Eq-ℤ-eq
d_Eq'45'ℤ'45'eq_136 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'ℤ'45'eq_136 = erased
-- elementary-number-theory.equality-integers.contraction-total-Eq-ℤ
d_contraction'45'total'45'Eq'45'ℤ_144 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_contraction'45'total'45'Eq'45'ℤ_144 = erased
-- elementary-number-theory.equality-integers.is-contr-total-Eq-ℤ
d_is'45'contr'45'total'45'Eq'45'ℤ_162 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'ℤ_162 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) erased)
      erased
-- elementary-number-theory.equality-integers.is-equiv-Eq-ℤ-eq
d_is'45'equiv'45'Eq'45'ℤ'45'eq_170 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Eq'45'ℤ'45'eq_170 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
