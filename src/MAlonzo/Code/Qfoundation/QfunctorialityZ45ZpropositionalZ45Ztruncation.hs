{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations

-- foundation.functoriality-propositional-truncation.unique-functor-trunc-Prop
d_unique'45'functor'45'trunc'45'Prop_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unique'45'functor'45'trunc'45'Prop_16 v0 v1 ~v2 ~v3 v4
  = du_unique'45'functor'45'trunc'45'Prop_16 v0 v1 v4
du_unique'45'functor'45'trunc'45'Prop_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_unique'45'functor'45'trunc'45'Prop_16 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_universal'45'property'45'trunc'45'Prop_164
      v0 v1
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
         v1 erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                 (coe v1)))
         (coe v2))
-- foundation.functoriality-propositional-truncation.functor-trunc-Prop
d_functor'45'trunc'45'Prop_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_functor'45'trunc'45'Prop_36 v0 v1 ~v2 ~v3 v4
  = du_functor'45'trunc'45'Prop_36 v0 v1 v4
du_functor'45'trunc'45'Prop_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_functor'45'trunc'45'Prop_36 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_unique'45'functor'45'trunc'45'Prop_16 (coe v0) (coe v1)
            (coe v2)))
-- foundation.functoriality-propositional-truncation.htpy-functor-trunc-Prop
d_htpy'45'functor'45'trunc'45'Prop_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'functor'45'trunc'45'Prop_50 = erased
-- foundation.functoriality-propositional-truncation.htpy-uniqueness-functor-trunc-Prop
d_htpy'45'uniqueness'45'functor'45'trunc'45'Prop_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'uniqueness'45'functor'45'trunc'45'Prop_66 = erased
-- foundation.functoriality-propositional-truncation.id-functor-trunc-Prop
d_id'45'functor'45'trunc'45'Prop_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_id'45'functor'45'trunc'45'Prop_78 = erased
-- foundation.functoriality-propositional-truncation.comp-functor-trunc-Prop
d_comp'45'functor'45'trunc'45'Prop_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'functor'45'trunc'45'Prop_100 = erased
-- foundation.functoriality-propositional-truncation.map-equiv-trunc-Prop
d_map'45'equiv'45'trunc'45'Prop_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'trunc'45'Prop_114 v0 v1 ~v2 ~v3 v4
  = du_map'45'equiv'45'trunc'45'Prop_114 v0 v1 v4
du_map'45'equiv'45'trunc'45'Prop_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'trunc'45'Prop_114 v0 v1 v2
  = coe
      du_functor'45'trunc'45'Prop_36 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         (coe v2))
-- foundation.functoriality-propositional-truncation.map-inv-equiv-trunc-Prop
d_map'45'inv'45'equiv'45'trunc'45'Prop_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'inv'45'equiv'45'trunc'45'Prop_126 v0 v1 ~v2 ~v3 v4
  = du_map'45'inv'45'equiv'45'trunc'45'Prop_126 v0 v1 v4
du_map'45'inv'45'equiv'45'trunc'45'Prop_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'inv'45'equiv'45'trunc'45'Prop_126 v0 v1 v2
  = coe
      du_map'45'equiv'45'trunc'45'Prop_114 (coe v1) (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v2))
-- foundation.functoriality-propositional-truncation.equiv-trunc-Prop
d_equiv'45'trunc'45'Prop_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'trunc'45'Prop_138 v0 v1 ~v2 ~v3 v4
  = du_equiv'45'trunc'45'Prop_138 v0 v1 v4
du_equiv'45'trunc'45'Prop_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'trunc'45'Prop_138 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'equiv'45'trunc'45'Prop_114 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
         (coe
            du_map'45'inv'45'equiv'45'trunc'45'Prop_126 (coe v0) (coe v1)
            (coe v2)))
