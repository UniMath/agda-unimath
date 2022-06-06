{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QexistentialZ45Zquantification where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations

-- foundation.existential-quantification.exists-Prop
d_exists'45'Prop_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_exists'45'Prop_12 ~v0 ~v1 ~v2 ~v3 = du_exists'45'Prop_12
du_exists'45'Prop_12 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_exists'45'Prop_12
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      () erased
-- foundation.existential-quantification.exists
d_exists_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_exists_32 = erased
-- foundation.existential-quantification.is-prop-exists
d_is'45'prop'45'exists_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'exists_44 ~v0 ~v1 ~v2 ~v3
  = du_is'45'prop'45'exists_44
du_is'45'prop'45'exists_44 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'exists_44
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_exists'45'Prop_12)
-- foundation.existential-quantification.∃-Prop
d_'8707''45'Prop_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_'8707''45'Prop_56 ~v0 ~v1 ~v2 ~v3 = du_'8707''45'Prop_56
du_'8707''45'Prop_56 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_'8707''45'Prop_56
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      () erased
-- foundation.existential-quantification.∃
d_'8707'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707'_70 = erased
-- foundation.existential-quantification.is-prop-∃
d_is'45'prop'45''8707'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45''8707'_82 ~v0 ~v1 ~v2 ~v3
  = du_is'45'prop'45''8707'_82
du_is'45'prop'45''8707'_82 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45''8707'_82
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_'8707''45'Prop_56)
-- foundation.existential-quantification.intro-exists
d_intro'45'exists_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_intro'45'exists_96 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_intro'45'exists_96 v4 v5
du_intro'45'exists_96 :: AgdaAny -> AgdaAny -> AgdaAny
du_intro'45'exists_96 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
      ()
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) (coe v1))
-- foundation.existential-quantification.intro-∃
d_intro'45''8707'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_intro'45''8707'_118 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_intro'45''8707'_118 v4 v5
du_intro'45''8707'_118 :: AgdaAny -> AgdaAny -> AgdaAny
du_intro'45''8707'_118 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
      ()
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) (coe v1))
-- foundation.existential-quantification.ev-intro-exists-Prop
d_ev'45'intro'45'exists'45'Prop_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_ev'45'intro'45'exists'45'Prop_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8
  = du_ev'45'intro'45'exists'45'Prop_138 v6 v7 v8
du_ev'45'intro'45'exists'45'Prop_138 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_ev'45'intro'45'exists'45'Prop_138 v0 v1 v2
  = coe v0 (coe du_intro'45'exists_96 (coe v1) (coe v2))
-- foundation.existential-quantification.elim-exists-Prop
d_elim'45'exists'45'Prop_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_elim'45'exists'45'Prop_164 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_elim'45'exists'45'Prop_164 v2 v5 v6
du_elim'45'exists'45'Prop_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_elim'45'exists'45'Prop_164 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe ()) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_ind'45'Σ_50
         (coe v2))
-- foundation.existential-quantification.is-equiv-ev-intro-exists-Prop
d_is'45'equiv'45'ev'45'intro'45'exists'45'Prop_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'ev'45'intro'45'exists'45'Prop_186 ~v0 ~v1 v2 ~v3
                                                   ~v4 v5
  = du_is'45'equiv'45'ev'45'intro'45'exists'45'Prop_186 v2 v5
du_is'45'equiv'45'ev'45'intro'45'exists'45'Prop_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'ev'45'intro'45'exists'45'Prop_186 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe du_elim'45'exists'45'Prop_164 (coe v0) (coe v1))
