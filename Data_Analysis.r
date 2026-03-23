#Set_Working_Directory
wkdir <- "C:\\Users\\Chetkar_Jha\\Documents\\Workspace\\Projects\\SMT\\DA\\DA_Markers"
setwd(wkdir)

#Library
library("Rtsne")
library("dplyr")
library("Seurat")

#####################################################
#Meta
#Inputs : a Seurat based count data
#Outputs: tSNE plot, Subgroups, Gene Markers
#####################################################



#Set_Local_Functions: helper functions and important subroutines
#Set Helper functions First

#Simple Case
lookup <- function(x){
	which(x==1)
}

lookup.c <- function(x){
	length(which(x==1))
}


#Returns g for estimated k
#Sanitizing only No modeling here
get.g <- function(g.orig,k){

	#Initialize
	g      <- g.orig

		##underfit-model
		if( max(g.orig) > k){
			ll     <- max(g.orig)
			kk     <- k +1
			for(l in kk:ll){
				ind.l 	<- which(g.orig == l)
				g[ind.l]<- floor(runif(1,1,k))
			}
		}

		#TrueModel
		if(k==max(g.orig)){
			g <- g.orig
		}

		##overfit-model
		if(max(g.orig) < k){
			nos      <- k - max(g.orig)
			ll.vec   <- round(runif(nos,1, max(g.orig)),0)
			ll.unq   <- sort(unique(ll.vec))
			j        <- max(g.orig)

			for(l in 1: length(ll.unq)){
				c.split <- length(which(ll.vec== ll.unq[l]))
				ind     <- which(g.orig == ll.unq[l])[-(1:2)]
				gg.pts  <- c(sort(sample(length(ind)-1,size=c.split,replace=FALSE)),length(ind))

				for(cc in 2:length(gg.pts)){
					j 			<- j + 1
					lower   	<- gg.pts[cc-1]

					ind.u       <- ind[lower:gg.pts[cc]]
					g[ind.u]    <- j
				}
			}
		}
		#Sanity Check
		status <- which( unlist(table(g)) <= 5)

		repeat{
			ind   <- which( unlist(table(g)) > 50)[1]
			index <- which(g == ind)

			start.index <- 1
			end.index   <- 5
			for(i in 1:max(g)){

				g[index[start.index : end.index]] <- i
				start.index <- start.index + 5
				end.index   <- end.index   + 5
			}

			status <- which( unlist(table(g)) <= 5)

			if(length(status)==0 ){
				break
			}
		}
g
}

#Returns B.est[1:K, 1:K] for a given K
get.Best <- function(A,g){
	k      <- max(g)
	B.est  <- matrix(0, k, k)

	for(i in 1:k){
		for(j in 1:i){

			ind.i <- which(g == i)
			ind.j <- which(g == j)
			ni <- length(ind.i)
			nj <- length(ind.j)

			if(i != j){

				if(ni > 1 & nj > 1){
					B.est[i,j] <- sum(A[ind.i,ind.j])/(ni*nj)
				}else{
					B.est[i,j] <- 0
				}


			}else{

				if(ni*nj > 1){
					B.est[i,i] <- sum(A[ind.i,ind.j])/(ni*(nj - 1))
				}else{
					B.est[i,i] <- 0
				}
			}
			}
		}

		B.est 		<- B.est + t(B.est)
		diag(B.est) <- diag(B.est)/2

		ind0 <- which(B.est == 0)
		ind1 <- which(B.est == 1)
		B.est[ind0] <- 0.001
		B.est[ind1] <- 0.999

B.est
}

##Helper function
mat.conn <- function(g){

	N <- length(g)
	mat <- matrix(0, N, N)

	for(i in 1:N){
		for(j in 1:N){

			if(g[i]== g[j]){
				mat[i,j] = 1
			}
		}
	}

mat
}

##############################################################################################
#Set Important Functions
#Yields Adjacency Matrix After Thresholding
##############################################################################################

est.comm <- function(cormat,cutoff){

  adj <- matrix(0, nrow(cormat), ncol(cormat))
  ind <- which(cormat >= quantile(cormat[upper.tri(cormat)],cutoff) )
  adj[ind]  <- 1
  diag(adj) <- rep(0,nrow(adj))

  adj[lower.tri(adj)] <- 0
  adj <- adj + t(adj)

adj
}

#SBM loglikelihood for a given K and adjacency matrix
#Used for hyperaparameter grid search
#Larger the likelihood more optimum the hyperparameter (including A which depends on the thresholding parameter)
loglik <- function(A, g, K){


	
	#out <- pl_est_com(A,K, parallel= TRUE)
	#g   <-out$class

	B.est <- matrix(0, K, K)
	B.est  <- get.Best(A,g)

	B.est  <- get.Best(A,g)
	tvec       <- rep(0, K)

	B         <- 1 - A
	diag(B)   <- rep(0, nrow(A))

	sum_log   <- 0

	for(l in 1:K){

		ind       <- which(g==l)
		n         <- length(ind)

		Tmp       <- matrix(0, n, n)
		P.tmp     <- B.est[l,l]

		sum_log	<- sum_log + sum(A[ind, ind])*log(P.tmp) + (sum(B[ind, ind]))*log(1- P.tmp)


   }

sum_log
}

##################################
#loglik for different hyperparam

llik_data <- function(data, delta, gamma, beta, kappa, alpha){
#Filtering
#Low_High_CellCount
sum.col <- apply(data,2,sum)
lower   <- quantile(sum.col, delta)
upper   <- quantile(sum.col, 1-delta)

#Multiple_Filters
ind.col  <- which( sum.col > lower & sum.col < upper)
data_gf  <- data[, ind.col]


### Compute standard deviation
sd.row <- apply(data_gf, 1, sd)

#Filtering
#Top 2000 genes
#Roughly 11 percent
ind.row <- which(sd.row > gamma)


sd.row  <- apply(data_gf, 1, sd)
ind.ref <- which(sd.row > 0.1)
data_gf <- data_gf[ind.ref, ]

data_f  <- log(1 + beta*data_gf/rowSums(data_gf))/log(2)
cor     <- cor(as.matrix(data_f))

A       <- est.comm(cor, kappa)
K       <- smt_A(A, alpha)[[2]]

llik	    <- loglik(A, g, K)
}

##############################################################################################
#Read the Data
##############################################################################################

data_tot      <- readRDS("hu_clean.RDS")

new_data_tot  <- UpdateSeuratObject(data_tot)
ind			  <- which(Idents(new_data_tot)=="Bipolar")

rm("data_tot")
data_bplr     <- new_data_tot[,ind]
counts        <- data_bplr[["RNA"]]$counts
data          <- as.matrix(counts)
############################################################################################
# Generate single cell data using Splatter
# using DCSBM
############################################################################################
library(splatter)
library(scater)

gen_data_scRNAseq <- function(N, d, ib.status, K, lib.loc, lib.scale, de.prob, out.prob){

if(ib.status == "ib1"){
	 group.prob = c(2/K, rep(1/K, K-1))  
	 group.prob = group.prob/sum(group.prob)
	 
  }else if (ib.status == "ib2"){
	 group.prob = c(2/K, 1/K, rep(1/(2*K), K-2))  
	 group.prob = group.prob/sum(group.prob)

	 }else{
		group.prob = rep(1/K, K)
   }

params <- setParams(params, list(
  batchCells = N,             
  nGenes    = d,                
  group.prob= group.prob,
  lib.loc = lib.loc,                   # Degree correction mean (theta)
  lib.scale = lib.scale,                # Degree correction variance
  de.prob = de.prob,                   # Probability of marker genes per block
  out.prob = out.prob
))

sce <- splatSimulate(params, method = "groups", verbose = FALSE)
out <- list()
out[[1]] <- data <- counts(sce)
out[[2]] <- as.numeric(factor(sce$Group))
	
out
}




###############################################################################################
# Grid Search
# Computes the optimum grid values for the likelihood function outputs g, K. 
# We also use this to output ari and K for comparison
###############################################################################################


#For simplicity, we do the grid search manually
#It can be easily automated
#The default value is (0)
delta <- 0.25
gamma <- 2000
beta <- 20000
kappa <- 0.65
alpha <- 0.05

############################
# Get A
############################

#Does a default grid search
#delta = used for trimming corruption
#gamma = used for selecting highly differentiable genes
#signal strength = large signal strength is better for noisy data
#kappa = threshold
#apha = 0.05


search_grid <- function(data, start.loglik=-10^20){

out       <- list()
delta.vec <- c(0.1, 0.15,0.2, 0.25, 0.3)
gamma.vec <- c(0, 0.25, 0.5, 0.75)
beta.vec  <- c(5000, 10000, 20000)
kappa.vec <- c(0.5, 0.65, 0.75 , 0.85, 0.95)
alpha.vec <- c(0.05)

llik_max <- lik_d <- start.loglik
count <- 0	
for(d in delta.vec){
	for(gam in gamma.vec){
		for(bet in beta.vec){
			for(kappa in kappa.vec){
				
				count <- count + 1
				print( paste("This is", count, "iteration at", date(), llik_max))
				#Low_High_CellCount
				sum.col <- apply(data,2,sum)
				lower   <- quantile(sum.col, delta)
				upper   <- quantile(sum.col, 1-delta)

				#Multiple_Filters
				ind.col  <- which( sum.col > lower & sum.col < upper)
				data_gf  <- data[, ind.col]
				
				#Filtering
				ind.row <- which(sd.row > quantile(gamma.vec, gam))
				sd.row  <- apply(data_gf, 1, sd)
				ind.ref <- which(sd.row > 0.1)
				data_gf <- data_gf[ind.ref, ]

				data_f  <- log(1 + beta*data_gf/rowSums(data_gf))/log(2)
				cor     <- cor(as.matrix(data_f))

				A       <- est.comm(cor, kappa)
				obj     <- smt_A(A, K_m =20, alpha)
                g       <- obj[[1]]
                K       <- obj[[2]]
				llik_curr <- llik	<- loglik(A, g, K)
							   
				
				if(llik_max <= llik_curr){
					out[[1]] = llik_max = llik_curr
					out[[2]] = A_return = A
					out[[3]] = g_return = g
					out[[4]] = K_return = K

					out[[5]] = delta_return = d
					out[[6]] = gamma_return = gam
					out[[7]] = beta_return  = bet
					out[[8]] = kappa_return = kappa
					print(paste("I am in the loop.", llik_max, llik_curr))
				}

			  llik_max = max(llik_max, llik_curr)
				
}
}
}
}
out
}




##############################################################################################
#tSNE plot


 tsne_obj <- Rtsne(A, initial_dims =100, partial_pca = TRUE, perplexity=30, check_duplicates = FALSE) # You can change the value of perplexity and see how the plot changes
 pdf("A_tsne.pdf")
 
 tsne_plot <- data.frame(x= tsne_obj$Y[,1], y = tsne_obj$Y[,2], g=g, center1 =center[g, 2], center2=center[g, 3])
 
 #Numbering the Cluster
 centeroids <- tsne_plot %>%group_by(as.factor(g))%>%summarise(x = mean(x), y = mean(y))
 ggplot(tsne_plot) + geom_point(aes(x=x, y=y, color=as.factor(g))) + geom_text(data = center, mapping= aes_string(x= center[,2], y=center[,3], label=1:17), color="black", size=4) + labs(x="First Dimension", y="Second Dimension", color="Subgroups", labels = g)
	
 dev.off()
 

#################################################################################################


bplr <- CreateSeuratObject(counts = data_gf)
bplr <- NormalizeData(object = bplr, normalization.method="LogNormalize", scale.factor =20000)
Idents(bplr) <- g

bplr.markers <- FindAllMarkers(object = bplr)
write.table(bplr.markers, "bplr_markers.csv",sep=",")
