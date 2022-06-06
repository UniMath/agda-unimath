{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qbooleans where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsets
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.booleans.bool
type T_bool_4 = Bool
d_bool_4 = ()
pattern C_false_8 = False
pattern C_true_6 = True
-- foundation.booleans.Eq-bool
d_Eq'45'bool_10 :: Bool -> Bool -> ()
d_Eq'45'bool_10 = erased
-- foundation.booleans.refl-Eq-bool
d_refl'45'Eq'45'bool_14 :: Bool -> AgdaAny
d_refl'45'Eq'45'bool_14 = erased
-- foundation.booleans.Eq-eq-bool
d_Eq'45'eq'45'bool_20 ::
  Bool ->
  Bool ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'eq'45'bool_20 = erased
-- foundation.booleans.eq-Eq-bool
d_eq'45'Eq'45'bool_28 ::
  Bool ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'bool_28 = erased
-- foundation.booleans.neq-false-true-bool
d_neq'45'false'45'true'45'bool_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'false'45'true'45'bool_30 = erased
-- foundation.booleans.neg-bool
d_neg'45'bool_32 :: Bool -> Bool
d_neg'45'bool_32 v0
  = if coe v0 then coe C_false_8 else coe C_true_6
-- foundation.booleans.conjunction-bool
d_conjunction'45'bool_34 :: Bool -> Bool -> Bool
d_conjunction'45'bool_34 v0 v1
  = if coe v0 then coe v1 else coe seq (coe v1) (coe v0)
-- foundation.booleans.disjunction-bool
d_disjunction'45'bool_36 :: Bool -> Bool -> Bool
d_disjunction'45'bool_36 v0 v1
  = if coe v0 then coe seq (coe v1) (coe v0) else coe v1
-- foundation.booleans.is-prop-Eq-bool
d_is'45'prop'45'Eq'45'bool_42 ::
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Eq'45'bool_42 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82
             else (\ v2 ->
                     coe
                       MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88)
      else (if coe v1
              then \ v2 ->
                     coe
                       MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
              else coe
                     MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82)
-- foundation.booleans.is-set-bool
d_is'45'set'45'bool_44 ::
  Bool ->
  Bool ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'bool_44 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qsets.du_is'45'set'45'prop'45'in'45'id_146
-- foundation.booleans.bool-Set
d_bool'45'Set_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_bool'45'Set_50
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'bool_44)
-- foundation.booleans.neq-neg-bool
d_neq'45'neg'45'bool_54 ::
  Bool ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'neg'45'bool_54 = erased
-- foundation.booleans.neg-neg-bool
d_neg'45'neg'45'bool_56 ::
  Bool -> MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'neg'45'bool_56 = erased
-- foundation.booleans.is-equiv-neg-bool
d_is'45'equiv'45'neg'45'bool_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'neg'45'bool_58
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'bool_32) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'bool_32) erased)
-- foundation.booleans.equiv-neg-bool
d_equiv'45'neg'45'bool_60 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'neg'45'bool_60
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_neg'45'bool_32) (coe d_is'45'equiv'45'neg'45'bool_58)
-- foundation.booleans.not-equiv-const
d_not'45'equiv'45'const_64 ::
  Bool ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_not'45'equiv'45'const_64 = erased
-- foundation.booleans.is-injective-const-true
d_is'45'injective'45'const'45'true_82 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'const'45'true_82 = erased
-- foundation.booleans.is-injective-const-false
d_is'45'injective'45'const'45'false_86 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'const'45'false_86 = erased
