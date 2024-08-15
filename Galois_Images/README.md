The `Magma` code in this folder assumes the user has access to the code present in Andrew Sutherland's `ell-adic-galois-images` repository, which can be found [*here*](https://github.com/AndrewVSutherland/ell-adic-galois-images).

This code verifies claims made about the ell-adic Galois images of CM elliptic curves as they appear in our paper.

`Index_Verification` verifies the claims made in Lemmas 3.2, 3.7, 3.10, and 3.13 of our paper. In particular, we verify that the the index of the 2-adic image of a CM elliptic curve with CM discriminants -4, -8, or -16 coincide with the index of the mod 8 image. We also verify that the index of the 3-adic image of an elliptic curve with CM discriminant -3 coincides with the index of the mod 9 image.

`Table_Verification_Code` confirms that the data provided in Tables 2 and 4 of our paper for ell-adic images of CM elliptic curves is correct.
WARNING: Certain computations in this code are time and memory intensive.

`Twist_Verification_Code` confirms that, for elliptic curves with CM by an order of class number 2, the elliptic curves listed in Tables 2 and 4 with non-maximal ell-adic images for some prime ell are the complete list of such curves. This code executes the method explained in Section 4, and the method is explained in more detail in Examples 4.4 and 4.5. 
WARNING: The final two lines of this code are time and memory intensive.


