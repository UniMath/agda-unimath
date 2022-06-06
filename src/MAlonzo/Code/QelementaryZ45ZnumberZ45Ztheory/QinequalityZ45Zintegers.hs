{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QinequalityZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes

-- elementary-number-theory.inequality-integers.leq-ℤ
d_leq'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_leq'45'ℤ_4 = erased
-- elementary-number-theory.inequality-integers.refl-leq-ℤ
d_refl'45'leq'45'ℤ_12 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_refl'45'leq'45'ℤ_12 = erased
-- elementary-number-theory.inequality-integers.antisymmetric-leq-ℤ
d_antisymmetric'45'leq'45'ℤ_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_antisymmetric'45'leq'45'ℤ_20 = erased
-- elementary-number-theory.inequality-integers.trans-leq-ℤ
d_trans'45'leq'45'ℤ_36 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trans'45'leq'45'ℤ_36 = erased
-- elementary-number-theory.inequality-integers.decide-leq-ℤ
d_decide'45'leq'45'ℤ_52 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_decide'45'leq'45'ℤ_52 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
      (coe (\ v2 -> v2)) erased
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_decide'45'is'45'nonnegative'45'ℤ_370
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdifferenceZ45Zintegers.d_diff'45'ℤ_4
            (coe v1) (coe v0)))
-- elementary-number-theory.inequality-integers.succ-leq-ℤ
d_succ'45'leq'45'ℤ_60 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_succ'45'leq'45'ℤ_60 = erased
-- elementary-number-theory.inequality-integers.leq-ℤ-succ-leq-ℤ
d_leq'45'ℤ'45'succ'45'leq'45'ℤ_68 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_leq'45'ℤ'45'succ'45'leq'45'ℤ_68 = erased
-- elementary-number-theory.inequality-integers.concatenate-eq-leq-eq-ℤ
d_concatenate'45'eq'45'leq'45'eq'45'ℤ_84 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'eq'45'leq'45'eq'45'ℤ_84 = erased
-- elementary-number-theory.inequality-integers.concatenate-leq-eq-ℤ
d_concatenate'45'leq'45'eq'45'ℤ_94 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'leq'45'eq'45'ℤ_94 = erased
-- elementary-number-theory.inequality-integers.concatenate-eq-leq-ℤ
d_concatenate'45'eq'45'leq'45'ℤ_106 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_concatenate'45'eq'45'leq'45'ℤ_106 = erased
-- elementary-number-theory.inequality-integers.le-ℤ
d_le'45'ℤ_112 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()
d_le'45'ℤ_112 = erased
-- elementary-number-theory.inequality-integers.preserves-order-add-ℤ'
d_preserves'45'order'45'add'45'ℤ''_124 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_preserves'45'order'45'add'45'ℤ''_124 = erased
-- elementary-number-theory.inequality-integers.preserves-order-add-ℤ
d_preserves'45'order'45'add'45'ℤ_138 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_preserves'45'order'45'add'45'ℤ_138 = erased
-- elementary-number-theory.inequality-integers.preserves-leq-add-ℤ
d_preserves'45'leq'45'add'45'ℤ_154 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_preserves'45'leq'45'add'45'ℤ_154 = erased
-- elementary-number-theory.inequality-integers.reflects-order-add-ℤ'
d_reflects'45'order'45'add'45'ℤ''_174 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_reflects'45'order'45'add'45'ℤ''_174 = erased
-- elementary-number-theory.inequality-integers.reflects-order-add-ℤ
d_reflects'45'order'45'add'45'ℤ_188 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny
d_reflects'45'order'45'add'45'ℤ_188 = erased
