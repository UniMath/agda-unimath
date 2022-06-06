{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qtruncations where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation

-- foundation.truncations.type-trunc
d_type'45'trunc_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.truncations.type-trunc"
-- foundation.truncations.is-trunc-type-trunc
d_is'45'trunc'45'type'45'trunc_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.truncations.is-trunc-type-trunc"
-- foundation.truncations.trunc
d_trunc_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trunc_22 v0 v1 ~v2 = du_trunc_22 v0 v1
du_trunc_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trunc_22 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'trunc'45'type'45'trunc_16 v0 v1 erased)
-- foundation.truncations.unit-trunc
d_unit'45'trunc_38
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.truncations.unit-trunc"
-- foundation.truncations.is-truncation-trunc
d_is'45'truncation'45'trunc_48
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.truncations.is-truncation-trunc"
-- foundation.truncations.equiv-universal-property-trunc
d_equiv'45'universal'45'property'45'trunc_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'trunc_60 v0 v1 v2 ~v3 v4
  = du_equiv'45'universal'45'property'45'trunc_60 v0 v1 v2 v4
du_equiv'45'universal'45'property'45'trunc_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'trunc_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation.du_precomp'45'Trunc_20
         (coe d_unit'45'trunc_38 v0 v2 erased))
      (coe d_is'45'truncation'45'trunc_48 v0 v1 v2 erased v3)
-- foundation.truncations.universal-property-trunc
d_universal'45'property'45'trunc_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'trunc_78 v0 v1 ~v2 v3
  = du_universal'45'property'45'trunc_78 v0 v1 v3
du_universal'45'property'45'trunc_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'trunc_78 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation.du_universal'45'property'45'truncation'45'is'45'truncation_212
      (coe v0) (coe d_unit'45'trunc_38 v0 v1 erased)
      (coe (\ v3 -> coe d_is'45'truncation'45'trunc_48 v0 v3 v1 erased))
      (coe v2)
-- foundation.truncations._.map-universal-property-trunc
d_map'45'universal'45'property'45'trunc_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'universal'45'property'45'trunc_98 v0 v1 v2 ~v3
  = du_map'45'universal'45'property'45'trunc_98 v0 v1 v2
du_map'45'universal'45'property'45'trunc_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'universal'45'property'45'trunc_98 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation.du_map'45'is'45'truncation_232
      (coe v0) (coe d_unit'45'trunc_38 v0 v2 erased)
      (coe (\ v3 -> coe d_is'45'truncation'45'trunc_48 v0 v3 v2 erased))
      (coe v1)
-- foundation.truncations._.triangle-universal-property-trunc
d_triangle'45'universal'45'property'45'trunc_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'universal'45'property'45'trunc_104 = erased
-- foundation.truncations._.apply-universal-property-trunc
d_apply'45'universal'45'property'45'trunc_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
d_apply'45'universal'45'property'45'trunc_110 v0 v1 v2 ~v3 v4 v5 v6
  = du_apply'45'universal'45'property'45'trunc_110 v0 v1 v2 v4 v5 v6
du_apply'45'universal'45'property'45'trunc_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_apply'45'universal'45'property'45'trunc_110 v0 v1 v2 v3 v4 v5
  = coe du_map'45'universal'45'property'45'trunc_98 v0 v1 v2 v4 v5 v3
-- foundation.truncations._.dependent-universal-property-trunc
d_dependent'45'universal'45'property'45'trunc_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'trunc_130 v0 v1 ~v2 ~v3
  = du_dependent'45'universal'45'property'45'trunc_130 v0 v1
du_dependent'45'universal'45'property'45'trunc_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'trunc_130 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation.du_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278
      (coe v0) (coe v1) (coe du_trunc_22 (coe v0) (coe v1))
      (coe d_unit'45'trunc_38 v0 v1 erased)
      (coe (\ v2 -> coe d_is'45'truncation'45'trunc_48 v0 v2 v1 erased))
-- foundation.truncations._.equiv-dependent-universal-property-trunc
d_equiv'45'dependent'45'universal'45'property'45'trunc_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'trunc_140 v0 v1
                                                           ~v2 ~v3 v4
  = du_equiv'45'dependent'45'universal'45'property'45'trunc_140
      v0 v1 v4
du_equiv'45'dependent'45'universal'45'property'45'trunc_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'trunc_140 v0 v1
                                                            v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation.du_precomp'45'Π'45'Truncated'45'Type_102
         (coe d_unit'45'trunc_38 v0 v1 erased))
      (coe du_dependent'45'universal'45'property'45'trunc_130 v0 v1 v2)
-- foundation.truncations._.apply-dependent-universal-property-trunc
d_apply'45'dependent'45'universal'45'property'45'trunc_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_apply'45'dependent'45'universal'45'property'45'trunc_154 v0 v1
                                                           ~v2 ~v3 v4
  = du_apply'45'dependent'45'universal'45'property'45'trunc_154
      v0 v1 v4
du_apply'45'dependent'45'universal'45'property'45'trunc_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_apply'45'dependent'45'universal'45'property'45'trunc_154 v0 v1
                                                            v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe
         du_equiv'45'dependent'45'universal'45'property'45'trunc_140
         (coe v0) (coe v1) (coe v2))
