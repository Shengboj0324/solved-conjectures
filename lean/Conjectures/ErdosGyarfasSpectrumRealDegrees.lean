import Conjectures.ErdosGyarfasSpectrumPlane
import Conjectures.ErdosGyarfasSpectrumBound

/-! The induced space counts exactly the real affine lines determined by the
other points. Distinct lines through a point have distinct finite traces. -/

namespace ErdosGyarfasSpectrum

private theorem mem_spans {P : Finset PlanePoint} {p : PlanePoint} {L : Set PlanePoint} :
    L∈GyarfasPlanar.spannedLines P p ↔ ∃ q∈P.erase p,lineSet p q=L := by
  classical
  exact Finset.mem_image

private theorem spanning_partner {P : Finset PlanePoint} {a b p : PlanePoint} (ha : a∈P) (hb : b∈P)
    (hne : b≠a) (hp : p∈lineSet a b) : ∃ q∈P.erase p,lineSet p q=lineSet a b := by
  classical
  by_cases eq : a=p
  · subst p; exact ⟨b,Finset.mem_erase.mpr ⟨hne,hb⟩,rfl⟩
  · exact ⟨a,Finset.mem_erase.mpr ⟨eq,ha⟩,common_line hne.symm (fun h => eq h.symm) hp (left_mem_affineSpan_pair ℝ a b)⟩

theorem trace_spans {P : Finset PlanePoint} {p : PlanePoint} (hp : p∈P) :
    (GyarfasPlanar.spannedLines P p).image (traceLine P)=(planarLines P).filter (p∈·) := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨q,hq,rfl⟩ := mem_spans.mp hL
    obtain ⟨ne,hq'⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_filter.mpr ⟨(mem_planarLines _ _).mpr ⟨p,hp,q,hq',ne,rfl⟩,
      (mem_trace _ _ _).mpr ⟨hp,left_mem_affineSpan_pair ℝ _ _⟩⟩
  · intro hl
    obtain ⟨hL,pl⟩ := Finset.mem_filter.mp hl
    obtain ⟨a,ha,b,hb,ne,rfl⟩ := (mem_planarLines _ _).mp hL
    obtain ⟨q,hq,eq⟩ := spanning_partner ha hb ne ((mem_trace _ _ _).mp pl).2
    exact Finset.mem_image.mpr ⟨_,mem_spans.mpr ⟨q,hq,rfl⟩,congrArg (traceLine P) eq⟩

theorem trace_injective (P : Finset PlanePoint) (p : PlanePoint) :
    Set.InjOn (traceLine P) (GyarfasPlanar.spannedLines P p : Set (Set PlanePoint)) := by
  classical
  intro L hL M hM eq
  obtain ⟨a,ha,rfl⟩ := mem_spans.mp hL
  obtain ⟨b,hb,rfl⟩ := mem_spans.mp hM
  obtain ⟨na,hap⟩ := Finset.mem_erase.mp ha
  obtain ⟨nb,_⟩ := Finset.mem_erase.mp hb
  have point := (mem_trace P (lineSet p a) a).mpr ⟨hap,right_mem_affineSpan_pair ℝ p a⟩
  rw [eq] at point
  exact common_line nb.symm na.symm (left_mem_affineSpan_pair ℝ p b) ((mem_trace _ _ _).mp point).2

theorem planar_degree {P : Finset PlanePoint} {p : PlanePoint} (hp : p∈P) :
    degree (planarLines P) p=(GyarfasPlanar.spannedLines P p).card := by
  classical
  rw [degree,←trace_spans hp,Finset.card_image_of_injOn (trace_injective P p)]

theorem real_degree_bound (P : Finset PlanePoint) (nc : ¬Collinear ℝ (P : Set PlanePoint)) :
    17*(P.image (fun p => (GyarfasPlanar.spannedLines P p).card)).card+13 ≤ 16*P.card := by
  have eq : degrees P (planarLines P)=P.image (fun p => (GyarfasPlanar.spannedLines P p).card) :=
    Finset.image_congr fun p hp => planar_degree hp
  simpa only [←eq] using spectrum_bound (plane_space P nc)

end ErdosGyarfasSpectrum
