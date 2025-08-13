### Sage implementation of code for LuCaNT 2025 paper Eperimental Evidence for Lehmer's Conjecture on Elliptic Curves
##  Note - some functions require pandas installed as "pd"
from sage.rings.number_field.bdd_height import bdd_height, bdd_height_iq
import glob
import pandas as pd
import pickle as pkl


## Given an elliptic curve and the modified CPS height bound, return the bound on discriminants that need to be searched, and the bound on points
#  Inputs: CPS_bound - modified CPS height bound; height - height of a point on E
#  Outputs: disc_bound - bound on discriminants that need to be searched
def get_disc_bound(CPS_bound, height):
  disc_bound = exp(4*log(2) + 4*CPS_bound + 4*height)
  return disc_bound.n().ceiling()

### This function takes all initial height datasets from the Magma output, and returns a single pandas dataframe
##  Inputs - <directory>, path to directory where datasets are stored
##  Outputs - <combined_df>, a dataframe with all data
def get_all_initial_height_data(directory):
  file_pattern = directory + "/InitialHeightData_*.txt"

  # Get list of all datasets
  file_list = glob.glob(file_pattern)

  # Read in all dataframes
  dataframes = [pd.read_csv(file, sep = ",", header = "infer") for file in file_list]

  # Combine all dataframes
  combined_df = pd.concat(dataframes, ignore_index = True)

  return combined_df


### This function computes all elements of a set of quadratic fields with discriminant in some (absolute value range) up to a given bound
##  Inputs - <directory>, path to directory where pickled elements will be stored; <lbound, ubound>, lower and upper bounds on discriminants; <height_bound>, bound on height
##  Outputs - <ele_dict>, pickled dictionary of elements w/ keys discriminants and entries lists of elements 
def get_nf_height_elements(directory, lbound, ubound, height_bound):
  # Create a dictionary to store lists for each discriminant
  ele_dict = {}
  R.<x> = QQ[]

  # For each fundamental discriminant, create a key together with the elements up to <height_bound>
  for pos_disc in [lbound..ubound]:
    # Check if we have a fundamental discriminant
    if pos_disc.is_fundamental_discriminant():
      # Make field
      K = NumberField(x^2 - pos_disc, 'a')
      if pos_disc < 0:
        # Make list to hold elements
        ele_dict[pos_disc] = []
        for ele in bdd_height_iq(K, height_bound):
          # Only store elements that are not already in QQ
          if ele.is_rational() == False:
            ele_dict[pos_disc].append(ele)
      # Same thing, but with call to <bdd_height> instead of <bdd_height_iq>
      if pos_disc > 0:
        # Make list to hold elements
        ele_dict[pos_disc] = []
        # Sometimes the default precision is too low, and we get a floating point error, so we have to increase it.
        # We don't want to do this always because of the computational cost, so we do the try except (these instances are rare).
        try:
          for ele in bdd_height(K, height_bound):
            # Only store elements that are not already in QQ
            if ele.is_rational() == False:
              ele_dict[pos_disc].append(ele)
        except:
          try:
            for ele in bdd_height(K, height_bound, precision = 200):
              # Only store elements that are not already in QQ
              if ele.is_rational() == False:
                ele_dict[pos_disc].append(ele)
          except:
            for ele in bdd_height(K, height_bound, precision = 1000):
              # Only store elements that are not already in QQ
              if ele.is_rational() == False:
                ele_dict[pos_disc].append(ele)

  pkl_file = open(directory + '/nf_elements_' + str(lbound) + "_" + str(ubound) + ".pkl", 'ab')
  pkl.dump(ele_dict, pkl_file)
  pkl_file.close()

  return 

### Function to read in all number field data
##  Input - Directory, path to directory where all files are stored
##  Output - combined_dict, dictionary with all data
def get_combined_nf_dict(directory):
  # Folder containing the .pkl files
  folder_path = directory

  combined_dict = {}

  for filename in os.listdir(folder_path):
    if filename.startswith("nf_elements_") and filename.endswith(".pkl"):
      file_path = os.path.join(folder_path, filename)
      with open(file_path, "rb") as f:
        data = pkl.load(f)
        if not isinstance(data, dict):
          raise ValueError(f"File {filename} does not contain a dictionary.")
        combined_dict.update(data)

  return combined_dict

### Function to find the smallest height point on an elliptic curve from a dictionary of small height points by discriminant
##  Input - E, elliptic curve; dict - dictionary whose keys are fundamental discriminants and values are lists of elements in the corresponding field
##  Output - point, discriminant, and height of smallest point
def min_ht_pt_E(small_ele_dict, E):

  # Initially, we don't know the height of any points on <E>
  min_ht = oo
  min_ht_pt = None
  min_ht_disc = None

  # We will need these rings later
  R.<x,y,z> = QQ[]
  S.<w> = QQ[]
  disc_bound = max([abs(k) for k in small_ele_dict.keys()])


  for d in small_ele_dict.keys():
    # Extend E
    K.<s> = QuadraticField(d)
    E_K = E.base_extend(K)
    # Loop over all elements of the associated quadratic field
    # We keep a list of elements that we have already checked, so that we don't double-check galois conjugates
    checked_eles = []
    for ele in small_ele_dict[d]:
      # Convert <ele> to element of the correct field - this works because both number fields were generated with square roots of the discriminant
      fixed_ele = ele[1]*a + ele[0]
      # If we have not already checked the Galois conjugate, look for a corresponding point on E
      if fixed_ele.galois_conjugate() not in checked_eles:
        checked_eles.append(fixed_ele)
        pts = E_K.lift_x(fixed_ele, all = True)
        # If there are any points with the corresponding x-coordinate, search them
        if len(pts) > 0:
          for pt in pts:
            # If the point is not a torsion point, and has smaller height, this is our new winner
            if pt.order() == oo:
              try:
                ht = pt.height()
              except:
                print(pt)
                breakpoint()
              if ht < min_ht:
                min_ht = ht
                min_ht_pt = pt
                min_ht_disc = d

  # Finally, check the heights of points with x-coordinate QQ with naive height at most 50 (this is the cutoff we have chosen to search for all curves)
  
  for num in [-50..50]:
    for denom in [1..50]:
      if gcd(num,denom) == 1:
        # Find quadratic field where point with x-coordinate <num/denom> is defined
        def_poly_E = E.defining_polynomial()
        # Get y-poly as single-variable polynomial
        y_poly_at_x = S(def_poly_E(num/denom, w, 1))
        # Create number corresponding number field - use 't' to denote different field
        L.<t> = NumberField(y_poly_at_x)
        # Check if discriminant is small enough: 
        if abs(L.discriminant()) < disc_bound:
          E_L = E.base_extend(L)
          pts = E_L.lift_x(num/denom, all = True)
          for pt in pts:
            if pt.order() == oo:
              ht = pt.height()
              if ht < min_ht:
                min_ht = ht
                min_ht_pt = pt
                min_ht_disc = L.discriminant()


  # Return result
  return [min_ht_disc, min_ht_pt, min_ht]

### Function to make a clean data set with all relevant bounds
##  Inputs: paths to dataset of initial points and to dataset of CPS height bound data
##  Output: merged data with discriminant bound and bound on number field element heights calculated
def combined_data(path_to_initial_data, path_to_Be_data):
  # Read in initial data
  initial_data = get_all_initial_height_data(path_to_initial_data)

  # Read in Be_data
  Be_data = pd.read_csv(path_to_Be_data, sep = ",", header = "infer")

  # merge data
  merged_data = pd.merge(Be_data, initial_data, on="CremonaReference")

  # Remove rows where no point of small height was found during the initial search (these have initial heigth 0)
  merged_data = merged_data[merged_data["InitialHeight"] > 0]

  # Get height search bound on points
  merged_data["point_height_bound"] = merged_data.apply(lambda row : exp(2*(row["CPS_bound_quadratic"] + row["InitialHeight"])), axis = 1)

  # Get disc search bound
  merged_data["disc_bound"] = merged_data.apply(lambda row : get_disc_bound(row["CPS_bound_quadratic"], row["InitialHeight"]), axis = 1)

  # Set provable flag
  merged_data["provable"] = merged_data.apply(lambda row : 1 if row["disc_bound"] < 10000 and row["point_height_bound"] < 50 else 0, axis = 1)

  return merged_data

### Function to calculate actual minimum height point in provable case
### Result is saved at <outfile_name>
##  Inputs - CremonaList, DiscriminantList - pickled lists of the relevant data (in the same order!), these can be saved by pickling the output of the <combined_data> function;
##           outfile_name - name for ouptut file; nf_dict - dictionary of small height points in quadratic fields
##  Output - .txt file saved at <outfile_name>
def final_computation(CremonaList, DiscriminantList, out_dir, nf_dict):

  # Loop over curves
  for index in [0..len(CremonaList)-1]:
    # Make E
    label = CremonaList[index]
    E = EllipticCurve(label)
    # Get discriminant bound
    disc_bound = DiscriminantList[index]
    # Make file for this curve
    with open(out_dir + "/" + label + ".txt", "w") as f:
      # Print headers
      print("CremonaReference,Discriminant,Point,Height", file = f)
      # Make smaller dictionary
      limited_dict = {k : v for k, v in nf_dict.items() if abs(k) <= disc_bound}
      # Get height data
      disc, pt, ht = min_ht_pt_E(limited_dict, E)

      print(f"{label},{disc},{pt},{ht}", file = f)

      # Close file for that curve
      f.close()


### This function takes all provable height datasets from the Magma output, and returns a single pandas dataframe, with strings replaced by sage objects
##  Inputs - <directory>, path to directory where datasets are stored
##  Outputs - <df_sage>, a dataframe with all data, and objects turned into sage objects
def get_all_provable_data(directory):
  file_pattern = directory + "/*.txt"

  # Get list of all datasets
  file_list = glob.glob(file_pattern)

  # Read in all dataframes
  dataframes = [pd.read_csv(file, sep = ",", header = "infer", dtype={"CremonaReference" : str}) for file in file_list]

  # Combine all dataframes
  combined_df = pd.concat(dataframes, ignore_index = True)

  # Clean data and replace strings with sage objects
  clean_df = clean_provable_data(combined_df)

  return combined_df

### This function converts input strings and floats to the relevant sage objects
##  Inputs: <df> - dataframe, read from magma output
##  Outputs: <df_sage> - dataframe, with sage objects as entries
def clean_provable_data(df):
  df_sage = df.copy()

  # Replace discriminant with sage int
  df_sage["Discriminant"] = df.apply(lambda row : ZZ(row["Discriminant"]) if row["Height"] not in ["E1", "E2"] else "NaN", axis = 1)

  # Replace Height with element of RDF
  df_sage["Height"] = df.apply(lambda row : RDF(row["Height"]) if row["Height"] not in ["E1", "E2"] else "E1" if row["Height"] == "E1" else "E2", axis = 1)

  # Replace point string with corresponding sage object
  df_sage["Point"] = df.apply(lambda row : convert_provable_point(row["CremonaReference"], row["Discriminant"], clean_point(row["Point"])) if row["Height"] not in ["E1", "E2"] else "NaN", axis = 1)  

  return df_sage


### This function turns a point given as a list of strings into a point on the reference elliptic curve
##  Inputs: <curveRef> - the CremonaDatabase reference for the elliptic curve, as a string
##    <disc> - the discriminant of the quadratic field where the point lives, given as an int
##    <P> - coordinates of the point, given as a list of strings with "s" being the squareroot of <disc> 
##  Outputs: the corresponding point as a point on the elliptic curve E base-changed to the quadratic field with discriminant <disc>
def convert_provable_point(curveRef, disc, P):
  # Generic Polynomial rings used later
  B.<t> = QQ[]
  R.<x,y,z> = QQ[]
  S.<w> = QQ[]

  E = EllipticCurve(curveRef)
  # If the point is defined over an extension of Q, build the extension and base change <E> to that extension
  if disc != 1:
    # If the x-coordinate of the point is defined over Q, then the meaning of the variable is a little different
    try:
      x_coord = sage_eval(P[0])
      if x_coord.is_rational():
        y_poly_at_x = S(E.defining_polynomial()(x_coord, w, 1))
        K.<s> = NumberField(y_poly_at_x)
        E_K = E.change_ring(K)
        curve_pt = E_K((x_coord, sage_eval(P[1],locals={'t':s})))
    except:
      K.<s> = NumberField(t^2 - disc)
      E_K = E.change_ring(K)
      try:
        curve_pt = E_K(sage_eval(P[0],locals={'s':s}),sage_eval(P[1],locals={'s':s}))
      except:
        breakpoint()
    
    reset('s')
    
  # Otherwise, just do the string parsing
  else:
    curve_pt = E(sage_eval(P[0]),sage_eval(P[1]))

  # Coerce coordinates to become a point on <E_K>
  return curve_pt


### This function turns a point, given as a string of magma output, to a list of the coordinates
##  Inputs: <pt_str> - point on an elliptic curve, given as string of magma output
##  Outputs: <pt_list> - list of coordinates as strings
def clean_point(P):
  # Remove beginning and ending parenthesis, then split at ":"s
  pt_list = P[1:len(P)-1].split(" : ")
  return pt_list
