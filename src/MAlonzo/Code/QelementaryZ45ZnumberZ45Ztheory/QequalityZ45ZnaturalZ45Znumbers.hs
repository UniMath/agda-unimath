{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsets
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QsetZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- elementary-number-theory.equality-natural-numbers.Eq-ℕ
d_Eq'45'ℕ_4 :: Integer -> Integer -> ()
d_Eq'45'ℕ_4 = erased
-- elementary-number-theory.equality-natural-numbers.is-prop-Eq-ℕ
d_is'45'prop'45'Eq'45'ℕ_18 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Eq'45'ℕ_18 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82
             _ -> \ v2 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> \ v3 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_is'45'prop'45'Eq'45'ℕ_18 (coe v2) (coe v3)
-- elementary-number-theory.equality-natural-numbers.refl-Eq-ℕ
d_refl'45'Eq'45'ℕ_30 :: Integer -> AgdaAny
d_refl'45'Eq'45'ℕ_30 = erased
-- elementary-number-theory.equality-natural-numbers.Eq-eq-ℕ
d_Eq'45'eq'45'ℕ_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'eq'45'ℕ_38 = erased
-- elementary-number-theory.equality-natural-numbers.eq-Eq-ℕ
d_eq'45'Eq'45'ℕ_46 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'ℕ_46 = erased
-- elementary-number-theory.equality-natural-numbers.is-set-ℕ
d_is'45'set'45'ℕ_56 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'ℕ_56 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qsets.du_is'45'set'45'prop'45'in'45'id_146
-- elementary-number-theory.equality-natural-numbers.ℕ-Set
d_ℕ'45'Set_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ℕ'45'Set_58
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'ℕ_56)
-- elementary-number-theory.equality-natural-numbers.is-decidable-Eq-ℕ
d_is'45'decidable'45'Eq'45'ℕ_64 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'Eq'45'ℕ_64 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
             _ -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v2 -> v2))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v3 -> v3))
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_is'45'decidable'45'Eq'45'ℕ_64 (coe v2) (coe v3)
-- elementary-number-theory.equality-natural-numbers.has-decidable-equality-ℕ
d_has'45'decidable'45'equality'45'ℕ_74 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'ℕ_74 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
      erased erased
      (coe d_is'45'decidable'45'Eq'45'ℕ_64 (coe v0) (coe v1))
-- elementary-number-theory.equality-natural-numbers.decidable-eq-ℕ
d_decidable'45'eq'45'ℕ_80 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_decidable'45'eq'45'ℕ_80 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_is'45'set'45'ℕ_56 v0 v1)
         (coe d_has'45'decidable'45'equality'45'ℕ_74 (coe v0) (coe v1)))
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-zero-ℕ
d_is'45'decidable'45'is'45'zero'45'ℕ_96 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'zero'45'ℕ_96 v0
  = coe
      d_has'45'decidable'45'equality'45'ℕ_74 (coe v0)
      (coe (0 :: Integer))
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-zero-ℕ'
d_is'45'decidable'45'is'45'zero'45'ℕ''_102 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'zero'45'ℕ''_102 v0
  = coe
      d_has'45'decidable'45'equality'45'ℕ_74 (coe (0 :: Integer))
      (coe v0)
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-nonzero-ℕ
d_is'45'decidable'45'is'45'nonzero'45'ℕ_108 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'nonzero'45'ℕ_108 v0
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'neg_234
      (coe d_is'45'decidable'45'is'45'zero'45'ℕ_96 (coe v0))
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-one-ℕ
d_is'45'decidable'45'is'45'one'45'ℕ_114 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'one'45'ℕ_114 v0
  = coe
      d_has'45'decidable'45'equality'45'ℕ_74 (coe v0)
      (coe (1 :: Integer))
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-one-ℕ'
d_is'45'decidable'45'is'45'one'45'ℕ''_120 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'one'45'ℕ''_120 v0
  = coe
      d_has'45'decidable'45'equality'45'ℕ_74 (coe (1 :: Integer))
      (coe v0)
-- elementary-number-theory.equality-natural-numbers.is-decidable-is-not-one-ℕ
d_is'45'decidable'45'is'45'not'45'one'45'ℕ_126 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'not'45'one'45'ℕ_126 v0
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'neg_234
      (coe d_is'45'decidable'45'is'45'one'45'ℕ_114 (coe v0))
-- elementary-number-theory.equality-natural-numbers.map-total-Eq-ℕ
d_map'45'total'45'Eq'45'ℕ_132 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'total'45'Eq'45'ℕ_132 ~v0 v1
  = du_map'45'total'45'Eq'45'ℕ_132 v1
du_map'45'total'45'Eq'45'ℕ_132 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'total'45'Eq'45'ℕ_132 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe addInt (coe (1 :: Integer)) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- elementary-number-theory.equality-natural-numbers.is-contr-total-Eq-ℕ
d_is'45'contr'45'total'45'Eq'45'ℕ_148 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'ℕ_148 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) erased)
      erased
-- elementary-number-theory.equality-natural-numbers.is-equiv-Eq-eq-ℕ
d_is'45'equiv'45'Eq'45'eq'45'ℕ_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Eq'45'eq'45'ℕ_164 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      v0 v1
-- elementary-number-theory.equality-natural-numbers.equiv-unit-trunc-ℕ-Set
d_equiv'45'unit'45'trunc'45'ℕ'45'Set_172 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'ℕ'45'Set_172
  = coe
      MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.d_equiv'45'unit'45'trunc'45'Set_342
      (coe ()) (coe d_ℕ'45'Set_58)
