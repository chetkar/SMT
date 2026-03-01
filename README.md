Our code implements sequential multiple testing for estimating the number of blocks or communities in the stochastic block models (SBMs).

The advantage of our approach is that it is relatively more resistant to the noise (or out-in ratio).

smt_only is a function that can estimates the number of components when we are simulating newtorking using the parameters.

smt_A is the function that implements our SMT method when the input matrix is given.

Data_Analysis.r implements a general way for implementing our approach for a single cell data. 

Particularly, Data_Analysis.r analyzes the bipolar retina file mentioned in the paper (the data file has to be downloaded from the instruction given in the paper) outputing the tSNE and biomarkers by optimizing the hyperparameter using the grid search based on the loglilikehood.
Please cite our paper when you use our method. 

https://arxiv.org/pdf/2507.15471
