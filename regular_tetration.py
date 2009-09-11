class RegularTetration:
    RegularTetration(b,fixpoint_number):
        """
	Counting fixpoints as follows:
        For b<e^(1/e): 
	  0 denotes the lower fixpoint on the real axis,
          1 denotes the upper fixed point on the real axis,
	  2 denotes the fixpoint in the upper halfplane closest to the real axis, 
          3 the second-closest, etc

	For b>e^(1/e): 
	  1 denotes the fixpoint in the upper halfplane closest to the real axis,
          2 the second-closest fixed point, etc.
        """
