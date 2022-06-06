{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QlogicalZ45Zequivalences where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.Qpropositions

-- foundation.logical-equivalences.iff-eq
d_iff'45'eq_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_iff'45'eq_10 ~v0 ~v1 ~v2 ~v3 = du_iff'45'eq_10
du_iff'45'eq_10 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_iff'45'eq_10
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0))
-- foundation.logical-equivalences.is-prop-iff
d_is'45'prop'45'iff_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'iff_20 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'prod_280
      (coe
         MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
         v0 v1
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v3)))
      (coe
         MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
         v1 v0
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v2)))
-- foundation.logical-equivalences.is-equiv-equiv-iff
d_is'45'equiv'45'equiv'45'iff_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'iff_34 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'equiv'45'iff_34
du_is'45'equiv'45'equiv'45'iff_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'iff_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences.du_iff'45'equiv_78)
-- foundation.logical-equivalences.equiv-equiv-iff
d_equiv'45'equiv'45'iff_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'equiv'45'iff_48 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'equiv'45'iff_48
du_equiv'45'equiv'45'iff_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'equiv'45'iff_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences.du_equiv'45'iff''_66)
      (coe du_is'45'equiv'45'equiv'45'iff_34)
-- foundation.logical-equivalences.is-prop-logical-equivalence
d_is'45'prop'45'logical'45'equivalence_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'logical'45'equivalence_66 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'prod_280
      (coe
         MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
         v0 v1
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v3)))
      (coe
         MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
         v1 v0
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v2)))
