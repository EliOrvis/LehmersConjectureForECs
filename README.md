This is the public repository for the paper "Experimental investigations on Lehmer's Conjecture for Elliptic Curves" by Sven Cats, John Michael Clark, Mar Curco Iranzo, Charlotte Dombrowsky, Krystal Maughan, and Eli Orvis.

The `MinHeight` datasets in `Data` are created from the `qdhts.m`, and contain data from a large search for small height points on quadratic fields.

The datasets in `Provable_curves` are created by conducting a search over all x-coordinates of small height over certain discriminants, with bounds set so that the result is provably the smallest over all quadratic fields.
In all cases, these confirm that the points found in the original search (i.e. those in the `MinHeight` datasets) are in fact the smallest over all quadratic fields.

To produce the `MinHeight` datasets, run the command `GetHeightData` from `qd_hts.m` in Magma v 21.2-2. To produce the datasets in `Provable_curves` run the function `final_computation` from `sage_implementation.sage` in Sage v 10.6.
Note that `final_computation` requires a dictionary of points of small height over quadratic number fields. The necessary data is stored in the folder `nf_data_to_50`, which was created using the function `get_nf_height_elements` in `sage_implementation.sage`, and can be read into Sage using `get_combined_nf_dict`. 
