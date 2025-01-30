import pandas as pd
import glob

### This function turns a point given as a list of strings into a point on the reference elliptic curve
##  Inputs: <curveRef> - the CremonaDatabase reference for the elliptic curve, as a string
##    <disc> - the discriminant of the quadratic field where the point lives, given as an int
##    <P> - coordinates of the point, given as a list of strings with "s" being the squareroot of <disc> 
##  Outputs: the corresponding point as a point on the elliptic curve E base-changed to the quadratic field with discriminant <disc>
def convert_point(curveRef, disc, P):
  E = EllipticCurve(curveRef)
  # If the point is defined over an extension of Q, build the extension and base change <E> to that extension
  if disc != 1:
    K.<s> = NumberField(x^2 - disc)
    E_K = E.change_ring(K)
    curve_pt = E_K(sage_eval(P[0],locals={'s':s}),sage_eval(P[1],locals={'s':s}))
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

### This function converts input strings and floats to the relevant sage objects
##  Inputs: <df> - dataframe, read from magma output
##  Outputs: <df_sage> - dataframe, with sage objects as entries
def clean_data(df):
  df_sage = df.copy()

  # Replace discriminant with sage int
  df_sage["Discriminant"] = df.apply(lambda row : ZZ(row["Discriminant"]) if row["Height"] not in ["E1", "E2"] else "NaN", axis = 1)

  # Replace Height with element of RDF
  df_sage["Height"] = df.apply(lambda row : RDF(row["Height"]) if row["Height"] not in ["E1", "E2"] else "E1" if row["Height"] == "E1" else "E2", axis = 1)

  # Replace point string with corresponding sage object
  df_sage["Point"] = df.apply(lambda row : convert_point(row["CremonaReference"], row["Discriminant"], clean_point(row["Point"])) if row["Height"] not in ["E1", "E2"] else "NaN", axis = 1)  

  # Replace provable flag with a sage integer
  df_sage["Provable"] = df.apply(lambda row : ZZ(row["Provable"]) if row["Height"] not in ["E1", "E2"] else "NaN", axis= 1)

  return df_sage

### This function takes all min height datasets from the Magma output, and returns a single pandas dataframe, with strings replaced by sage objects
##  Inputs - <directory>, path to directory where datasets are stored
##  Outputs - <df_sage>, a dataframe with all data, and objects turned into sage objects
def get_all_height_data(directory):
  file_pattern = directory + "/MinHeightData_*.txt"

  # Get list of all datasets
  file_list = glob.glob(file_pattern)

  # Read in all dataframes
  dataframes = [pd.read_csv(file, sep = ",", header = "infer") for file in file_list]

  # Combine all dataframes
  combined_df = pd.concat(dataframes, ignore_index = True)

  # Clean data and replace strings with sage objects
  clean_df = clean_data(combined_df)

  return clean_df

### This function takes as input the Cremona reference for an elliptic curve (as a string), and outputs the max of the logarithmic height of j(E), the log norm of the discriminant of E, and 1
### See Silverman's AEC, Conjecture 9.9.
##  Inputs - <reference>, Cremona reference for an elliptic curve, as a string
##  Outputs - <lang_const>, constant described above
def get_lang_conj_const(reference):
  # Create the elliptic curve
  E = EllipticCurve(reference)

  # Create the appropriate constant for E
  # Note that since we are considering curves defined over Q, but taking K to be a quadratic extension, the norm is just the discriminant squared
  # Also, all curves in the Cremona database already are already with minimal discriminant.
  lang_const = max([1, E.j_invariant().height().log(), (E.discriminant()^2).log()])

  return lang_const


### This function adds a column to the dataframe created by <get_all_height_data> (above) that gives the smallest value of h(P)[Q(P) : Q].
### This is necessary since it is possible that there is a point P defined over Q with h(P') < h(P) < 2h(P') for all P' defined over a quadratic extension
##  Inputs - <df>, a Pandas dataframe matching the output format from <get_all_height_data>, recip (optional) - if <True>, adds 1/constant instead of constant 
##  Outputs - <df_lehmer>, a Pandas dataframe with the new column added.
def add_lehmer_constant(df, recip = False):
  # Make a copy of the dataframe
  df_lehmer = df.copy()

  # helper function
  def min_lehmer_point(CremonaRef, Discriminant, Height):
    E = EllipticCurve(CremonaRef)
    if Discriminant == 1:
      if recip:
        return 1/Height
      else:
        return Height
    else:
      # First, find the CPS height bound for E/Q
      CPS = E.CPS_height_bound()

      # Find the canonical height of all points of sufficiently small naive height over Q
      small_height_Q_pts = [P.height() for P in E.point_search(Height + CPS)]

      # Return either twice the height found, or the smallest height of one of the rational points found, if smaller
      if recip:
        return 1/(min([2*Height] + small_height_Q_pts))
      else:
        return min([2*Height] + small_height_Q_pts)

  # Add new column
  df_lehmer["LehmerConst"] = df.apply(lambda row : min_lehmer_point(row["CremonaReference"], row["Discriminant"], row["Height"]) , axis = 1)

  return df_lehmer