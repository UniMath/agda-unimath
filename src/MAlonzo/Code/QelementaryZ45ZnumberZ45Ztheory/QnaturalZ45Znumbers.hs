{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QnaturalZ45Znumbers where

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
import qualified MAlonzo.Code.Qfoundation.Qbooleans
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QwZ45Ztypes

-- elementary-number-theory.natural-numbers.ℕ
d_ℕ_4 = ()
data T_ℕ_4 = C_zero'45'ℕ_6 | C_succ'45'ℕ_8 Integer
-- elementary-number-theory.natural-numbers.is-zero-ℕ
d_is'45'zero'45'ℕ_10 :: Integer -> ()
d_is'45'zero'45'ℕ_10 = erased
-- elementary-number-theory.natural-numbers.is-zero-ℕ'
d_is'45'zero'45'ℕ''_14 :: Integer -> ()
d_is'45'zero'45'ℕ''_14 = erased
-- elementary-number-theory.natural-numbers.is-successor-ℕ
d_is'45'successor'45'ℕ_18 :: Integer -> ()
d_is'45'successor'45'ℕ_18 = erased
-- elementary-number-theory.natural-numbers.is-nonzero-ℕ
d_is'45'nonzero'45'ℕ_24 :: Integer -> ()
d_is'45'nonzero'45'ℕ_24 = erased
-- elementary-number-theory.natural-numbers.is-one-ℕ
d_is'45'one'45'ℕ_28 :: Integer -> ()
d_is'45'one'45'ℕ_28 = erased
-- elementary-number-theory.natural-numbers.is-one-ℕ'
d_is'45'one'45'ℕ''_32 :: Integer -> ()
d_is'45'one'45'ℕ''_32 = erased
-- elementary-number-theory.natural-numbers.is-not-one-ℕ
d_is'45'not'45'one'45'ℕ_36 :: Integer -> ()
d_is'45'not'45'one'45'ℕ_36 = erased
-- elementary-number-theory.natural-numbers.is-not-one-ℕ'
d_is'45'not'45'one'45'ℕ''_40 :: Integer -> ()
d_is'45'not'45'one'45'ℕ''_40 = erased
-- elementary-number-theory.natural-numbers.Nat-𝕎
d_Nat'45'𝕎_44 :: ()
d_Nat'45'𝕎_44 = erased
-- elementary-number-theory.natural-numbers.zero-Nat-𝕎
d_zero'45'Nat'45'𝕎_46 ::
  MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12
d_zero'45'Nat'45'𝕎_46
  = coe
      MAlonzo.Code.Qfoundation.QwZ45Ztypes.du_constant'45'𝕎_76
      (coe MAlonzo.Code.Qfoundation.Qbooleans.C_false_8) erased
-- elementary-number-theory.natural-numbers.succ-Nat-𝕎
d_succ'45'Nat'45'𝕎_48 ::
  MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12 ->
  MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12
d_succ'45'Nat'45'𝕎_48 v0
  = coe
      MAlonzo.Code.Qfoundation.QwZ45Ztypes.C_tree'45'𝕎_26
      (coe MAlonzo.Code.Qfoundation.Qbooleans.C_true_6)
      (coe (\ v1 -> v0))
-- elementary-number-theory.natural-numbers.ind-ℕ
d_ind'45'ℕ_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (Integer -> ()) ->
  AgdaAny -> (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_ind'45'ℕ_62 ~v0 ~v1 v2 v3 v4 = du_ind'45'ℕ_62 v2 v3 v4
du_ind'45'ℕ_62 ::
  AgdaAny -> (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_ind'45'ℕ_62 v0 v1 v2
  = case coe v2 of
      0 -> coe v0
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe v1 v3 (coe du_ind'45'ℕ_62 (coe v0) (coe v1) (coe v3))
-- elementary-number-theory.natural-numbers.is-injective-succ-ℕ
d_is'45'injective'45'succ'45'ℕ_74 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'succ'45'ℕ_74 = erased
-- elementary-number-theory.natural-numbers.is-nonzero-succ-ℕ
d_is'45'nonzero'45'succ'45'ℕ_98 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'succ'45'ℕ_98 = erased
-- elementary-number-theory.natural-numbers.is-nonzero-is-successor-ℕ
d_is'45'nonzero'45'is'45'successor'45'ℕ_104 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'is'45'successor'45'ℕ_104 = erased
-- elementary-number-theory.natural-numbers.is-successor-is-nonzero-ℕ
d_is'45'successor'45'is'45'nonzero'45'ℕ_110 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'successor'45'is'45'nonzero'45'ℕ_110 v0
  = case coe v0 of
      0 -> coe
             (\ v1 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
                  erased)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (\ v2 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                  (coe v1) erased)
-- elementary-number-theory.natural-numbers.has-no-fixed-points-succ-ℕ
d_has'45'no'45'fixed'45'points'45'succ'45'ℕ_124 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_has'45'no'45'fixed'45'points'45'succ'45'ℕ_124 = erased
-- elementary-number-theory.natural-numbers.is-nonzero-one-ℕ
d_is'45'nonzero'45'one'45'ℕ_128 ::
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'one'45'ℕ_128 = erased
-- elementary-number-theory.natural-numbers.is-not-one-zero-ℕ
d_is'45'not'45'one'45'zero'45'ℕ_130 ::
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'one'45'zero'45'ℕ_130 = erased
-- elementary-number-theory.natural-numbers.is-not-one-two-ℕ
d_is'45'not'45'one'45'two'45'ℕ_132 ::
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'one'45'two'45'ℕ_132 = erased
-- elementary-number-theory.natural-numbers.Nat-𝕎-ℕ
d_Nat'45'𝕎'45'ℕ_134 ::
  Integer -> MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12
d_Nat'45'𝕎'45'ℕ_134 v0
  = case coe v0 of
      0 -> coe d_zero'45'Nat'45'𝕎_46
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe d_succ'45'Nat'45'𝕎_48 (coe d_Nat'45'𝕎'45'ℕ_134 (coe v1))
-- elementary-number-theory.natural-numbers.ℕ-Nat-𝕎
d_ℕ'45'Nat'45'𝕎_138 ::
  MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12 -> Integer
d_ℕ'45'Nat'45'𝕎_138 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QwZ45Ztypes.C_tree'45'𝕎_26 v1 v2
        -> if coe v1
             then coe
                    addInt (coe (1 :: Integer))
                    (coe d_ℕ'45'Nat'45'𝕎_138 (coe v2 erased))
             else coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.natural-numbers.issec-ℕ-Nat-𝕎
d_issec'45'ℕ'45'Nat'45'𝕎_144 ::
  MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'ℕ'45'Nat'45'𝕎_144 = erased
-- elementary-number-theory.natural-numbers._.H
d_H_154 ::
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
   MAlonzo.Code.Qfoundation.QwZ45Ztypes.T_𝕎_12) ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_H_154 = erased
-- elementary-number-theory.natural-numbers.isretr-ℕ-Nat-𝕎
d_isretr'45'ℕ'45'Nat'45'𝕎_158 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'ℕ'45'Nat'45'𝕎_158 = erased
-- elementary-number-theory.natural-numbers.is-equiv-Nat-𝕎-ℕ
d_is'45'equiv'45'Nat'45'𝕎'45'ℕ_162 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Nat'45'𝕎'45'ℕ_162
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe d_ℕ'45'Nat'45'𝕎_138) erased erased
-- elementary-number-theory.natural-numbers.equiv-Nat-𝕎-ℕ
d_equiv'45'Nat'45'𝕎'45'ℕ_164 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Nat'45'𝕎'45'ℕ_164
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_Nat'45'𝕎'45'ℕ_134) (coe d_is'45'equiv'45'Nat'45'𝕎'45'ℕ_162)
-- elementary-number-theory.natural-numbers.is-equiv-ℕ-Nat-𝕎
d_is'45'equiv'45'ℕ'45'Nat'45'𝕎_166 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'ℕ'45'Nat'45'𝕎_166
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe d_Nat'45'𝕎'45'ℕ_134) erased erased
-- elementary-number-theory.natural-numbers.equiv-ℕ-Nat-𝕎
d_equiv'45'ℕ'45'Nat'45'𝕎_168 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'ℕ'45'Nat'45'𝕎_168
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_ℕ'45'Nat'45'𝕎_138) (coe d_is'45'equiv'45'ℕ'45'Nat'45'𝕎_166)
