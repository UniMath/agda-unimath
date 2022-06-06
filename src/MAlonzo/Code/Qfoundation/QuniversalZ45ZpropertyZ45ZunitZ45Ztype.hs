{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZunitZ45Ztype where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.universal-property-unit-type.ev-star
d_ev'45'star_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> AgdaAny) ->
  AgdaAny
d_ev'45'star_10 ~v0 ~v1 v2 = du_ev'45'star_10 v2
du_ev'45'star_10 ::
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> AgdaAny) ->
  AgdaAny
du_ev'45'star_10 v0 = coe v0 erased
-- foundation.universal-property-unit-type.ev-star'
d_ev'45'star''_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> AgdaAny) ->
  AgdaAny
d_ev'45'star''_20 ~v0 ~v1 = du_ev'45'star''_20
du_ev'45'star''_20 ::
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> AgdaAny) ->
  AgdaAny
du_ev'45'star''_20 = coe du_ev'45'star_10
-- foundation.universal-property-unit-type.pt
d_pt_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> AgdaAny
d_pt_32 ~v0 ~v1 v2 ~v3 = du_pt_32 v2
du_pt_32 :: AgdaAny -> AgdaAny
du_pt_32 v0 = coe v0
-- foundation.universal-property-unit-type.dependent-universal-property-unit
d_dependent'45'universal'45'property'45'unit_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'unit_42 ~v0
  = du_dependent'45'universal'45'property'45'unit_42
du_dependent'45'universal'45'property'45'unit_42 ::
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'unit_42 v0
  = coe
      MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_dependent'45'universal'45'property'45'contr'45'is'45'contr_256
-- foundation.universal-property-unit-type.equiv-dependent-universal-property-unit
d_equiv'45'dependent'45'universal'45'property'45'unit_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'unit_50 ~v0 ~v1
  = du_equiv'45'dependent'45'universal'45'property'45'unit_50
du_equiv'45'dependent'45'universal'45'property'45'unit_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'unit_50
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ev'45'star_10)
      (coe du_dependent'45'universal'45'property'45'unit_42 erased)
-- foundation.universal-property-unit-type.universal-property-unit
d_universal'45'property'45'unit_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'unit_60 ~v0 ~v1
  = du_universal'45'property'45'unit_60
du_universal'45'property'45'unit_60 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'unit_60
  = coe du_dependent'45'universal'45'property'45'unit_42 erased
-- foundation.universal-property-unit-type.equiv-universal-property-unit
d_equiv'45'universal'45'property'45'unit_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'unit_70 ~v0 ~v1
  = du_equiv'45'universal'45'property'45'unit_70
du_equiv'45'universal'45'property'45'unit_70 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'unit_70
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ev'45'star''_20) (coe du_universal'45'property'45'unit_60)
-- foundation.universal-property-unit-type.is-equiv-pt-is-contr
d_is'45'equiv'45'pt'45'is'45'contr_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pt'45'is'45'contr_82 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'pt'45'is'45'contr_82
du_is'45'equiv'45'pt'45'is'45'contr_82 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'pt'45'is'45'contr_82
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'equiv'45'is'45'contr_238
      (coe
         MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'contr'45'unit_42)
-- foundation.universal-property-unit-type.is-equiv-pt-universal-property-unit
d_is'45'equiv'45'pt'45'universal'45'property'45'unit_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pt'45'universal'45'property'45'unit_100 ~v0 ~v1 v2
                                                         v3
  = du_is'45'equiv'45'pt'45'universal'45'property'45'unit_100 v2 v3
du_is'45'equiv'45'pt'45'universal'45'property'45'unit_100 ::
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'pt'45'universal'45'property'45'unit_100 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'is'45'equiv'45'precomp_446
      (coe ()) erased (coe (\ v2 -> v0))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor''_510
              (coe du_ev'45'star''_20) (coe du_universal'45'property'45'unit_60)
              (coe v1 v2 v3)))
-- foundation.universal-property-unit-type.universal-property-unit-is-equiv-pt
d_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 ~v0 ~v1 v2
                                                         v3 ~v4 ~v5
  = du_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 v2 v3
du_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe
         MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
         (\ v2 -> v0) v1 erased)
      (coe du_universal'45'property'45'unit_60)
-- foundation.universal-property-unit-type.universal-property-unit-is-contr
d_universal'45'property'45'unit'45'is'45'contr_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'unit'45'is'45'contr_148 ~v0 ~v1 v2 ~v3
                                                   ~v4
  = du_universal'45'property'45'unit'45'is'45'contr_148 v2
du_universal'45'property'45'unit'45'is'45'contr_148 ::
  AgdaAny ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'unit'45'is'45'contr_148 v0 v1
  = coe
      du_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 (coe v0)
      (coe du_is'45'equiv'45'pt'45'is'45'contr_82)
-- foundation.universal-property-unit-type.is-equiv-diagonal-is-equiv-pt
d_is'45'equiv'45'diagonal'45'is'45'equiv'45'pt_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'diagonal'45'is'45'equiv'45'pt_166 ~v0 ~v1 v2 v3
                                                   ~v4 ~v5
  = du_is'45'equiv'45'diagonal'45'is'45'equiv'45'pt_166 v2 v3
du_is'45'equiv'45'diagonal'45'is'45'equiv'45'pt_166 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'diagonal'45'is'45'equiv'45'pt_166 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'is'45'section_668
      (coe (\ v2 -> coe v2 v0))
      (coe
         du_universal'45'property'45'unit'45'is'45'equiv'45'pt_124 (coe v0)
         (coe v1))
