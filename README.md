# This repository contains the following:

## Data 
- Raw datafiles organized by conductor
  - Each file has the name "MinHeightData_`conductor`.txt", where `conductor` is the conductor of the elliptic curves in that file
  - The contents of the datafields are described in the accompanying paper. To recap, values are separated by commas, with the first line containing headers. The data fields are:
    - `CremonaReference`: The label of the elliptic curve in the Cremona Database.
    - `Discriminant`: The discriminant of the number field Q(P), where P is the point of smallest height found during our search.
    - `Point`: Coordinates of the point of smallest height found during our search. The variable `s` is a square root of the value in the `Discriminant` field.
    - `Height`: The canonical height of the point in the `Point` column.
    - `Provable`: Flag indicating if the point is provably the smallest canonical height over all extensions of degree at most 2 (1), or only the smallest found in a search of discriminants at most 1,000 (0). 
- Pickled pandas datasets containing only curves where a point has been found, and with the constant in Lehmers conjecture added as an additional column
  - These files have names "Lehmer_data_`range_start`_`range_end`.pkl", where `range_start` and `range_end` indicate the range of indices from an original dataset, NOT the corresponding conductors etc. 

## Programs 
- Magma file "qdhts.m" which was used to collect the raw data
  - Running the function `GetHeightData(a,b)` creates a `MinHeightData_n.txt` for each `n` between `a` and `b`.
  - This file also contains the code used for the modified version of the CPS height bound.
- Sage file "Sage_postprocessing.sage" which was used to do the investigations into our dataset
  - The function `get_all_height_data(directory)` creates a single pandas dataframe containing all the data in files "MinHeightData_*.txt" located in the input `directory`.
  - The functions `add_lehmer_const` and `get_lang_const` can be used to compute the constants in Lehmer's and Lang's conjecture relevant to each curve.
 
## Notes
- The data was collected running Magma V2.21-2
- A small number of datasets added an extra line break during writing to the `.txt` files - these were removed manually, as they interfer with the Sage code to read in all height data.
- The Figures in the accompanying paper were produced using `pandas` and `matplotlib` through the terminal, all the code used for data manipulations is available in the `Sage_postprocessing.sage` file.    
