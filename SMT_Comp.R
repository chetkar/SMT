 ########################################################################
## Goal
## 1. To generate block model with sparse communities
## 2. Perform New Test
## 3. Also, propose new community detection method : spectral clustering with group lasso (penalization)
########################################################################
#wkdir <- "/Users/HAL9000/Documents/HypothesisTesting"
#setwd(wkdir)


library(irlba)
library(multiviewtest)
library(randnet)
library(fastRG)
library(devtools)
#devtools::install_github("RoheLab/gdim", force= TRUE)
library(RMTstat)
library(Rcpp)
library(RcppArmadillo)
library(Rcsdp)

library("RSpectra")
library(randnet)
library(RMTstat)
library("multiviewtest")

kclust <- function(A, k){

 N        <- nrow(A)
 init.obj <- kmeans(A, centers=k, iter.max= 100, nstart=10)
 init.g   <- init.obj$cluster
 ind <- evec     <- list()


 for(l in 1:k){
	ind[[l]]       <- which(init.g==l)
	evec[[l]]      <- eigs_sym(A[ ind[[l]], ind[[l]] ], 2)$vectors[,1]
 }

 gg <- init.g
 ss <- matrix(NA, N, k)

 for(i in 1:N){
	for(j in 1:k){
			ss[i,j] = sum( (A[i, ind[[j]] ] - evec[[j]] )^2 )
		}
		gg[i] <- which(ss[i,] == min(ss[i,]))
	}
 init.gg <- gg

}


#Simple Case
lookup <- function(x){
	which(x==1)
}

lookup.c <- function(x){
	length(which(x==1))
}

########
# Test performs new test
# It outputs K.hat
####

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

##
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

# Computes Manhattan Distance
mat.dist <- function(mat1, mat2){

	N <- ncol(mat)
	ans <- sum(abs(mat1-mat2)/N^2)
ans
}

eig.spacing <- function(){

}

mat.lap <- function(A){
D <- diag(0, ncol(A))

for(i in 1:ncol(D)){
	D[i,i] = sum(A[i,])
}

D
}

nb <- function(A){

	c.out <-  BHMC.estimate(A, K_m)$K
	out   <-  reg.SP(A, K = c.out)
	g     <-  out$cluster

g
}

lookup.c <- function(x){
	length(which(x==1))
}

#SBM Generator
gen.sbm <- function(rho, B, N, K){

	A <- P <- matrix(NA, N, N)

	#Generating partition
	g.gen     <- rmultinom(N, size= 1, prob= rho)
	g.ind	  <- unlist(apply(g.gen, 1, lookup))
	g.count	  <- unlist(apply(g.gen, 1, lookup.c))
	g         <- rep(seq(1, K,1), g.count)
	g         <- g[order(g.ind)]


	#Generating Adjacency
	P     <- B[g,g]
	vec.P <- as.vector(P)
	A     <- matrix(rbinom(rep(1,length(vec.P)),1, vec.P), N, N)
	diag(A) <- rep(0,N)
	#making symmetric
	A[lower.tri(A)] <-0
	A <- A + t(A)

	out   <- list(A,P,g)

out
}



######
smt_A <- function(A, K_m, method="1",alpha=0.05){

    update.g <- TRUE
    res      <- 1

    B         <- matrix(A, nrow(A), nrow(A))
    B         <- 1 - A
    diag(B)   <- rep(0, nrow(A))

  #seq.vec  <- seq(35, 5, -5)

	for(k in 10:K_m){

   if(k ==1){
      g <- rep(1, nrow(A))
   }else{


    if(method=="1"){
		  out    <- pl_est_com(A, K=k, max.iter=1000)
		  g      <- out$class

      }else{

        out     <- reg.SP(A, K=k)
        g       <- out$cluster
      }

    }

    if( sum(table(g) <= 10) > 0 | length(table(g)) < k ){
      upper_indx      <- 10*k
      g[1:upper_indx] <- rep(seq(1,k, 1),10)
    }


    out     <- reg.SP(A, K=k)
    g       <- out$cluster

      #out    <- pl_est_com(A, K=k, max.iter=1000)
      #g      <- out$class

      B.est <- matrix(0, k, k)
      B.est  <- get.Best(A,g)

  		B.est  <- get.Best(A,g)
      B.est[which(B.est<0.1)]=0.1
      B.est[which(B.est > 0.9)]=0.9
      tvec      <- rep(0, k)


  		for(l in 1:k){

  			ind       <- which(g==l)
  			n         <- length(ind)
  			P.tmp     <- B.est[l,l]

        if(P.tmp <= 0.5 ){

              Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
  			      diag(Tmp) <- rep(0, n)

  			      mu        <- n*sum(A[ind,ind])/(n*(n-1))
  			      #t1        <- n^(2/3)*max(eigs_sym(Tmp, 10)$values[2] - 2 - 1/(mu))
              t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
              #t1        <- n^(2/3)*max(irlba(Tmp,2,2, work=10)$d[2] - 2 - 1/(mu))


           }else{

              Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
  			      diag(Tmp) <- rep(0,n)

  			      mu        <- n*sum(B[ind,ind])/(n*(n-1))
  			      #t1        <- n^(2/3)*max(eigs_sym(Tmp,10)$values[2] - 2 - 1/(mu))
              t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
             #t1        <- n^(2/3)*max(irlba(Tmp,2, 2, work=20)$d[2] - 2 - 1/(mu))

  		  }

      tvec[l]   <- t1
      }

  		test.stat     <- max( tvec )

      print(c(k, tvec))
      print(Sys.time())



    if(!is.na(test.stat)){

      if( test.stat <= qtw(1-alpha/(k)) & update.g == TRUE ){

			   res       <- k
			   update.g  = FALSE
			   break
		    }
    }

	}

  out <- list()
	ans <- h.out   <- unlist(res)[1]
  out[[1]] <- g
  out[[2]] <- ans

out
}


smt_only <- function(K, lambda, Beta, N, K_m, alpha=0.05, scale.fac=1.05){

A      <- BlockModel.Gen(lambda=lambda, beta=Beta, n = N, K = K)$A
alpha    <- 0.05
res      <- 1
update.g <- TRUE
#############################
# Sequential Test Procedure
#############################


for(k in 2:K_m){

 if(k ==1){
    g <- rep(1, nrow(A))
 }else{
    out    <- pl_est_com(A, K=k)
    g      <- out$class

    #out     <- reg.SP(A, K=k)
    #g       <- out$cluster

  }


  if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
      upper_indx      <- 3*k
      g[1:upper_indx] <- rep(seq(1,k, 1),3)
  }

  B.est <- matrix(0, k, k)
  B.est  <- get.Best(A,g)

  B.est  <- get.Best(A,g)
  P.est  <- B.est[g,g]
  ind    <- which( P.est < 10^(-30))
  P.est[ind] <- 10^(-30)

  tvec      <- rep(0, k)

  B         <- 1 - A
  diag(B)   <- rep(0, nrow(A))

  for(l in 1:k){

    ind       <- which(g==l)
    n         <- length(ind)
    P.tmp     <- P.est[ind, ind][1]

    Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
    diag(Tmp) <- rep(0, length(ind))

    mu        <- n*sum(A[ind,ind])/(n*(n-1))
    t1        <- n^(2/3)*max(eigs_sym(Tmp,2)$values[2] - 2 - 1/(mu))

    Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
    diag(Tmp) <- rep(0, length(ind))

    mu        <- n*sum(B[ind,ind])/(n*(n-1))
    t2        <- n^(2/3)*max(eigs_sym(Tmp,2)$values[2] - 2 - 1/(mu))

    tvec[l]   <- max(t1, t2)
  }

  test.stat     <- max( tvec )

  if(!is.na(test.stat)){

    if( test.stat <= qtw(1-alpha/(2*k)) & update.g == TRUE ){

       res       <- k
       update.g  = FALSE
       break
      }
  }

}

h.out   <- unlist(res)[1]

h.out
}



######
smt_large <- function(K, lambda, Beta, N, K_m, alpha=0.05, scale.fac=1.05){


	A      <- BlockModel.Gen(lambda=lambda, beta=Beta, n = N, K = K)$A

	a.out  <- unlist(BHMC.estimate(A, K_m)$K)[1]

  B      <- Matrix(A, sparse = TRUE)
  f.out  <- eigcv(B, k_max=K_m)[1]

	ans 	<- c( a.out, f.out)
  ans   <- unlist(ans)

ans
}



######
smt <- function(K, lambda, Beta, N, K_m, alpha=0.05, scale.fac=1.05){


	A      <- BlockModel.Gen(lambda=lambda, beta=Beta, n = N, K = K)$A

	a.out  <- unlist(BHMC.estimate(A, K_m)$K)[1]
	b.out  <- unlist(LRBIC(A, K_m, lambda = NULL, model = "SBM")$SBM.K)[1]
	ncv    <- NCV.select(A, max.K=K_m, cv=3)
	c.out  <- unlist(which.min(ncv$l2))[1]
	ecv    <- ECV.block(A, max.K = K_m, B=3, holdout.p =0.1, tau=0, dc.est=2, kappa= NULL)
	d.out  <- unlist(which.min(ecv$l2))[1]
  e.out  <- StGoF(A, K_max= K_m)[1]
  B      <- Matrix(A, sparse = TRUE)
  f.out  <- eigcv(B, k_max=K_m)[1]

	update.g <- TRUE

	#############################
	# Sequential Test Procedure
	#############################
	res <- 1
	for(k in 1:K_m){

    if(k ==1){
        g <- rep(1, nrow(A))
      }else{

        #out    <- pl_est_com(A, K=k, max.iter=100)
        #g      <- out$class
        out     <- reg.SP(A, K=k)
        g       <- out$cluster



      }

    if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
        upper_indx      <- 3*k
        g[1:upper_indx] <- rep(seq(1,k, 1),3)
      }

      B.est <- matrix(0, k, k)
      B.est  <- get.Best(A,g)

		 A.est <- P.est      <- B.est[g,g]
		 ind                 <- which( P.est < 10^(-30))
     P.est[ind]          <- 10^(-30)
		 tvec                <- rep(NA, k)
		 B                   <- 1 - A
		 diag(B)             <- rep(0, nrow(A))
     B.est               <- get.Best(A,g)
		 P.est               <- B.est[g,g]
		 diag(A.est)         <- rep(0, N)
		 tvec                <- rep(0, k)

		    A.est      <- (A - P.est)/(sqrt( (N-1)*P.est*(1 - P.est) ))
		    test.stat <- max( N^(2/3)*(eigen(A.est)$values[1]-2), N^(2/3)*(-eigen(A.est)$values[N]-2) )


        if( test.stat <= qtw(1-alpha/2,beta=1) & update.g == TRUE ){
			     res <- k
			     update.g = FALSE
			     break
			  }
      }

	g.out    <- unlist(res)[1]

  alpha    <- 0.05
	res      <- 1
	update.g <- TRUE
	#############################
	# Sequential Test Procedure
	#############################

	for(k in 2:K_m){

   if(k ==1){
      g <- rep(1, nrow(A))
   }else{
		  out    <- pl_est_com(A, K=k, max.iter=100)
		  g      <- out$class
      #out     <- reg.SP(A, K=k)
      #g       <- out$cluster

    }

    if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
      upper_indx      <- 3*k
      g[1:upper_indx] <- rep(seq(1,k, 1),3)
    }

    B.est <- matrix(0, k, k)
    B.est  <- get.Best(A,g)

		P.est  <- B.est[g,g]
		ind    <- which( P.est < 10^(-30))
		P.est[ind] <- 10^(-30)

		tvec      <- rep(0, k)

		B         <- 1 - A
		diag(B)   <- rep(0, nrow(A))
    for(l in 1:k){

      ind       <- which(g==l)
      n         <- length(ind)
      P.tmp     <- B.est[l,l]

      if(P.tmp <= 0.5 ){

        if(P.tmp < 0){

           t1 <- 0

          }else{

            Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
            diag(Tmp) <- rep(0, n)

            mu        <- n*sum(A[ind,ind])/(n*(n-1))
            #t1        <- n^(2/3)*max(eigs_sym(Tmp, 10)$values[2] - 2 - 1/(mu))
            t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
            #t1        <- n^(2/3)*max(irlba(Tmp,2,2, work=10)$d[2] - 2 - 1/(mu))

            #t2 <- 0
         }

         }else{

          if(P.tmp > 1){

            t1 <- 0

          }else{

            Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
            diag(Tmp) <- rep(0,n)

            mu        <- n*sum(B[ind,ind])/(n*(n-1))
            #t1        <- n^(2/3)*max(eigs_sym(Tmp,10)$values[2] - 2 - 1/(mu))
           t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
           #t1        <- n^(2/3)*max(irlba(Tmp,2, 2, work=20)$d[2] - 2 - 1/(mu))
          }
      }

    tvec[l]   <- t1
    }

    test.stat     <- max( tvec )

    if(!is.na(test.stat)){

      if( test.stat <= qtw(1-alpha/(k)) & update.g == TRUE ){

			   res       <- k
			   update.g  = FALSE
			   break
		    }
    }

	}

	h.out   <- unlist(res)[1]

  alpha <- 0.01
  res      <- 1
	update.g <- TRUE
	#############################
	# Sequential Test Procedure
	#############################

	for(k in 1:K_m){

  if(k ==1){
     g <- rep(1, nrow(A))
  }else{
     out    <- pl_est_com(A, K=k, max.iter=100)
      g      <- out$class
   }

   if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
     upper_indx      <- 3*k
     g[1:upper_indx] <- rep(seq(1,k, 1),3)
   }
   B.est <- matrix(0, k, k)
   B.est  <- get.Best(A,g)
   for(l in 1:k){

     ind       <- which(g==l)
     n         <- length(ind)
     P.tmp     <- B.est[l,l]

     if(P.tmp <= 0.5 ){

       if(P.tmp < 0){

          t1 <- 0

         }else{

           Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
           diag(Tmp) <- rep(0, n)

           mu        <- n*sum(A[ind,ind])/(n*(n-1))
           #t1        <- n^(2/3)*max(eigs_sym(Tmp, 10)$values[2] - 2 - 1/(mu))
           t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
           #t1        <- n^(2/3)*max(irlba(Tmp,2,2, work=10)$d[2] - 2 - 1/(mu))

           #t2 <- 0
        }

        }else{

         if(P.tmp > 1){

           t1 <- 0

         }else{

           Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
           diag(Tmp) <- rep(0,n)

           mu        <- n*sum(B[ind,ind])/(n*(n-1))
           #t1        <- n^(2/3)*max(eigs_sym(Tmp,10)$values[2] - 2 - 1/(mu))
          t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
          #t1        <- n^(2/3)*max(irlba(Tmp,2, 2, work=20)$d[2] - 2 - 1/(mu))
         }
     }

   tvec[l]   <- t1
   }

   test.stat     <- max( tvec )

    if(!is.na(test.stat)){
		if( test.stat <= qtw(1-alpha/(k)) & update.g == TRUE ){

			res       <- k
			update.g  = FALSE
			break
		}
    }
	}

	i.out   <- unlist(res)[1]



  alpha <- 0.05
  res      <- 1
  update.g <- TRUE
  #############################
  # Sequential Test Procedure
  #############################

  for(k in 1:K_m){

   if(k ==1){
      g <- rep(1, nrow(A))
   }else{
      #out    <- pl_est_com(A, K=k, max.iter=100)
       #g      <- out$class

       out     <- reg.SP(A, K=k)
       g       <- out$cluster
    }

    if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
      upper_indx      <- 3*k
      g[1:upper_indx] <- rep(seq(1,k, 1),3)
    }

    B.est <- matrix(0, k, k)
    B.est  <- get.Best(A,g)

    for(l in 1:k){

      ind       <- which(g==l)
      n         <- length(ind)
      P.tmp     <- B.est[l,l]

      if(P.tmp <= 0.5 ){

        if(P.tmp < 0){

           t1 <- 0

          }else{

            Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
            diag(Tmp) <- rep(0, n)

            mu        <- n*sum(A[ind,ind])/(n*(n-1))
            #t1        <- n^(2/3)*max(eigs_sym(Tmp, 10)$values[2] - 2 - 1/(mu))
            t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
            #t1        <- n^(2/3)*max(irlba(Tmp,2,2, work=10)$d[2] - 2 - 1/(mu))

            #t2 <- 0
         }

         }else{

          if(P.tmp > 1){

            t1 <- 0

          }else{

            Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
            diag(Tmp) <- rep(0,n)

            mu        <- n*sum(B[ind,ind])/(n*(n-1))
            #t1        <- n^(2/3)*max(eigs_sym(Tmp,10)$values[2] - 2 - 1/(mu))
           t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
           #t1        <- n^(2/3)*max(irlba(Tmp,2, 2, work=20)$d[2] - 2 - 1/(mu))
          }
      }

    tvec[l]   <- t1
    }

    test.stat     <- max( tvec )

    if(!is.na(test.stat)){

      if( test.stat <= qtw(1-alpha/(k)) & update.g == TRUE ){

         res       <- k
         update.g  = FALSE
         break
        }
    }

  }

  jj.out   <- unlist(res)[1]

  alpha <- 0.01
  res      <- 1
  update.g <- TRUE
  #############################
  # Sequential Test Procedure
  #############################

  for(k in 1:K_m){

  if(k ==1){
     g <- rep(1, nrow(A))
  }else{
     #out    <- pl_est_com(A, K=k, max.iter=100)
      #g      <- out$class
      out     <- reg.SP(A, K=k)
      g       <- out$cluster
   }

   if( sum(table(g) < 3) > 0 | length(table(g)) < k ){
     upper_indx      <- 3*k
     g[1:upper_indx] <- rep(seq(1,k, 1),3)
   }

   B.est <- matrix(0, k, k)
   B.est  <- get.Best(A,g)

   for(l in 1:k){

     ind       <- which(g==l)
     n         <- length(ind)
     P.tmp     <- B.est[l,l]

     if(P.tmp <= 0.5 ){

       if(P.tmp < 0){

          t1 <- 0

         }else{

           Tmp       <- A[ind, ind]/( sqrt( (n)* P.tmp*(1- P.tmp) ))
           diag(Tmp) <- rep(0, n)

           mu        <- n*sum(A[ind,ind])/(n*(n-1))
           #t1        <- n^(2/3)*max(eigs_sym(Tmp, 10)$values[2] - 2 - 1/(mu))
           t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
           #t1        <- n^(2/3)*max(irlba(Tmp,2,2, work=10)$d[2] - 2 - 1/(mu))

           #t2 <- 0
        }

        }else{

         if(P.tmp > 1){

           t1 <- 0

         }else{

           Tmp       <- (B[ind, ind])/( sqrt( (n)* P.tmp*(1- P.tmp) ))
           diag(Tmp) <- rep(0,n)

           mu        <- n*sum(B[ind,ind])/(n*(n-1))
           #t1        <- n^(2/3)*max(eigs_sym(Tmp,10)$values[2] - 2 - 1/(mu))
          t1        <- n^(2/3)*max(eigen(Tmp)$values[2] - 2 - 1/(mu))
          #t1        <- n^(2/3)*max(irlba(Tmp,2, 2, work=20)$d[2] - 2 - 1/(mu))
         }
     }

   tvec[l]   <- t1
   }

   test.stat     <- max( tvec )

    if(!is.na(test.stat)){
    if( test.stat <= qtw(1-alpha/(k)) & update.g == TRUE ){


      res       <- k
      update.g  = FALSE
      break
    }
    }
  }

  kk.out   <- unlist(res)[1]

	ans 	<- c( a.out, b.out, c.out, d.out, e.out, f.out, g.out, h.out, i.out, jj.out, kk.out)
  ans   <- unlist(ans)

ans
}


prop.fn <- function(x,K){

	out <- length( which(x==K))/length(x)
out

}

unitcomp_large <- function(sc){

library(Matrix)
library(multiviewtest)
library(randnet)
library(RMTstat)
library(RSpectra)

		lambda    <- lambda.vec[sc]
		N         <- N.vec[sc]
		K         <- K.vec[sc]
		K_m       <- K_m.vec[sc]
		Beta      <- Beta.vec[sc]

		alpha      <- 0.05
		m          <- 100
		k_rep      <- rep(K,m)

		out     <- sapply(k_rep, smt_only, lambda, Beta, N = N, K_m = K_m, alpha)

out
}


unitcomp <- function(sc){

library(Matrix)
library(multiviewtest)
library(randnet)
library(fastRG)
#install.packages("devtools")
#install.packages("remotes")
library(RMTstat)
library(Rcpp)
library(RcppArmadillo)
library(Rcsdp)
library(kernlab)

library(RSpectra)
library(randnet)
library(RMTstat)
library(multiviewtest)

library(remotes)
library(devtools)
#devtools::install_github("RoheLab/gdim")
library(gdim)
library(rARPACK)



		lambda    <- lambda.vec[sc]
		N         <- N.vec[sc]
		K         <- K.vec[sc]
		K_m       <- K_m.vec[sc]
		Beta      <- Beta.vec[sc]

		alpha      <- 0.05
		m          <- 100
		k_rep      <- rep(K,m)


		out1     <- sapply(k_rep, smt, lambda, Beta, N = N, K_m = K_m, alpha)
		out     <- apply(out1, 1, prop.fn, K)

out
}


unitcomp_large <- function(sc){

library(Matrix)
library(multiviewtest)
library(randnet)
library(RMTstat)

library(RSpectra)
library(randnet)
library(RMTstat)
library(multiviewtest)
library(irlba)



		lambda    <- lambda.vec[sc]
		N         <- N.vec[sc]
		K         <- K.vec[sc]
		K_m       <- K_m.vec[sc]
		Beta      <- Beta.vec[sc]

		alpha      <- 0.05
		m          <- 100
		k_rep      <- rep(K,m)


		out     <- sapply(k_rep, smt_only, lambda, Beta, N = N, K_m = K_m, alpha)


out
}

##################################
##################################
        library(foreach)
        library(doParallel)
        no_cores <- 8
        cl       <- makeCluster(no_cores)
        registerDoParallel(cl)

        library(RMTstat)
        library(randnet)
        library(kernlab)
        library(multiviewtest)
        library(rARPACK)

        N.vec      <- rep(c(200), each=48)
        K_m.vec    <- rep(c(10), each=48)
        K.vec      <- rep( c(2,3, 4), each=16)
        Beta.vec   <- rep( c( rep( c(0), each=4), rep( c(0.2), each=4), rep(c(0.4), each=4), rep(c(0.6), each=4)), 3)
        lambda.vec <- rep( c(10, 20, 40, 80), 12)


        Comp_200 <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass')%dopar%
            unitcomp(sc)

        stopCluster(cl)
        print(Sys.time())

        write.table(Comp_200, "Comparison_200_bet_all_new.csv", sep=",")



    library(foreach)
    library(doParallel)
    no_cores <- 8
    cl       <- makeCluster(no_cores)
    registerDoParallel(cl)

    library(RMTstat)
    library(randnet)
    library(kernlab)
    library(multiviewtest)
    library(rARPACK)

    N.vec      <- rep(c(500), each=48)
    K_m.vec    <- rep(c(10), each=48)
    K.vec      <- rep( c(2,3, 4), each=16)
    Beta.vec   <- rep( c( rep( c(0), each=4), rep( c(0.2), each=4), rep(c(0.4), each=4), rep(c(0.6), each=4)), 3)
    lambda.vec <- rep( c(10, 20, 40, 80), 12)


    Comp_500 <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass')%dopar%
        unitcomp(sc)

    stopCluster(cl)
    print(Sys.time())

    write.table(Comp_500, "Comparison_500_bet_all_new.csv", sep=",")


    library(foreach)
    library(doParallel)
    no_cores <- 8
    cl       <- makeCluster(no_cores)
    registerDoParallel(cl)

    library(RMTstat)
    library(randnet)
    library(kernlab)
    library(multiviewtest)
    library(rARPACK)

    N.vec      <- rep(c(1000), each=48)
    K_m.vec    <- rep(c(10), each=48)
    K.vec      <- rep( c(2,3, 4), each=16)
    Beta.vec   <- rep( c( rep( c(0), each=4), rep( c(0.2), each=4), rep(c(0.4), each=4), rep(c(0.6), each=4)), 3)
    lambda.vec <- rep( c(10, 20, 40, 80), 12)


    Comp_1000 <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass')%dopar%
        unitcomp(sc)

    stopCluster(cl)
    print(Sys.time())

    write.table(Comp_1000, "Comparison_1000_bet_all_new.csv", sep=",")


print(Sys.time())

    library(foreach)
    library(doParallel)
    no_cores <- 8
    cl       <- makeCluster(no_cores)
    registerDoParallel(cl)

    library(RMTstat)
    library(randnet)
    library(kernlab)
    library(multiviewtest)
    library(rARPACK)

    N.vec      <- rep(c(1000), each=48)
    K_m.vec    <- rep(c(8), each=36)
    K.vec      <- rep( c(5,6,7), each=16)
    Beta.vec   <- rep( c( rep( c(0), each=4), rep( c(0.2), each=4), rep(c(0.4), each=4), rep(c(0.6), each=4)), 3)
    lambda.vec <- rep( c(10, 20, 40, 80), 12)


    Comp_1000_highK <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass')%dopar%
        unitcomp(sc)

    stopCluster(cl)
    print(Sys.time())

    write.table(Comp_1000_highK, "Comparison_1000_bet_all_highK.csv", sep=",")



    print(Sys.time())
    write.table(Comp_1000_highK, "Comp_1000_highK.csv", sep=",")





    power.fn <- function(x, K){

      out1 <- length(which(x >=  K) )/ length(x)
      out2 <- length(which(x >  K) )/ length(x)
      out  <- c(out1, out2)


out
}


library(foreach)
library(doParallel)
no_cores <- 8
cl       <- makeCluster(no_cores)
registerDoParallel(cl)

library(RMTstat)
library(randnet)
library(multiviewtest)

N.vec      <- rep(c(5000), each=24)
K.vec      <- rep( c(10,20,30), each=8)
K_m.vec    <- K.vec + 10
Beta.vec   <- rep( c( rep( c(0), each=4), rep( c(0.2), each=4)),3)
lambda.vec <- rep( c(100, 200, 400, 800), 6)


Comp_5000_highK <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass')%dopar%
    unitcomp_large(sc)

stopCluster(cl)
print(Sys.time())

write.table(Comp_5000_highK, "Comp_5000_highK_SMT.csv", sep=",")



unitcomp_power <- function(sc){

            library(RMTstat)
            library(randnet)
            library(kernlab)
            library(multiviewtest)
            library(rARPACK)
            library(RSpectra)

            lambda    <- lambda.vec[sc]
            N         <- N.vec[sc]
            K         <- K.vec[sc]
            K_m       <- K_m.vec[sc]
            Beta      <- Beta.vec[sc]

            alpha      <- 0.05
            m          <- 100
            k_rep      <- rep(K,m)


            out1     <- sapply(k_rep, smt_only, lambda, Beta, N = N, K_m = K_m, alpha)
            out     <-  apply(sapply(out1, power.fn, K), 1, sum)/m
out
}



  N.vec      <- rep(c(500, 1000, 2000, 5000), 9)
  K.vec      <- rep(c(2, 4, 6), each =12)
  lambda.vec <- N.vec^(2/3)
  #lambda.vec <- rep(c(100),each=36)
  Beta.vec   <- rep(rep(c(0, 0.1, 0.2), each=4),3)
  K_m.vec    <- rep(c(8), each=36)


    library(foreach)
            library(doParallel)
            no_cores <- 8
            cl       <- makeCluster(no_cores)
            registerDoParallel(cl)

            library(RMTstat)
            library(randnet)
            library(kernlab)
            library(multiviewtest)
            library(rARPACK)
            Power <- foreach(sc = 1:length(N.vec), .combine = rbind, .errorhandling = 'pass' )%dopar%
                        unitcomp_power(sc)

            stopCluster(cl)
            print(Sys.time())


write.table(Power, "Power_new.csv", sep=",")
