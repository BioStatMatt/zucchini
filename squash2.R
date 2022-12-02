## The coding in this R script is based primarily on the 
## theory and descriptions provided in the following article:
## William DuMouchel, Chris Volinsky, Theodore Johnson, 
## Corinna Cortes, and Daryl Pregibon. 1999. Squashing flat 
## files flatter. In Proceedings of the fifth ACM SIGKDD
## international conference on Knowledge discovery and data 
## mining (KDD '99). Association for Computing Machinery, 
## New York, NY, USA, 6-15. DOI:https://doi.org/10.1145/312129.312184

## Major updates to squash.R:
## 1. Initializes squashed data set with moments at 0 (weighted) variances equal
## to 1 
## 2. Calculates up to 4th order moments with numeric gradients
## 3. Allows for squashing in parallel by passing a cluster object (e.g. "cl") 
## to squash.data.frame()
## 4. Allows for missing values through p-squashing or e-squashing


## formula for computing reduced samples size
reduced_sample_size <- function(n, alpha){
  min(floor(max(1, alpha*log(n, 2))),n)
}
  

## Functions to return unique elements from coskew and cokurtosis matrices
## Adapted from M3.MM and M4.MM functions in PerformanceAnalytics package
## Takes in a pre-centered matrix, Xc
coskew <- function(Xc) 
{
  .Call("M3sample", Xc, nrow(Xc), ncol(Xc), 1, PACKAGE = "PerformanceAnalytics")
}

cokurtosis <- function(Xc) 
{
  # The c code function scales the moments 
  .Call("M4sample", Xc, nrow(Xc), ncol(Xc), PACKAGE = "PerformanceAnalytics")*nrow(Xc)
}


## compute up to fourth order moments for specified data
## function does not allow for missing values, but is faster than 
## compute_moments_miss, which does
## 
## dat - a data frame with only numeric variables,
##       including a numeric 'weight' column
## degree - degree of moments
compute_moments <- function(dat, degree = 4) {
  
  ## extract weights (last column)
  wgt <- dat[,ncol(dat), drop = TRUE]
  dsc <- dat[,-ncol(dat), drop = FALSE]

  ## compute weighted sums (for weighted mean)
  cen <- (rep(1,nrow(dsc))%*%(wgt*dsc))[1,]
  
  ## compute weighted moments up to second order
  cvnc <- crossprod(dsc*sqrt(wgt))
  mmt <- c(sum(wgt), cen, diag(cvnc), cvnc[lower.tri(cvnc)])

  if(degree >= 3){
    ## compute weighted moments up to third order
    mmt <- c(mmt, coskew(dsc*wgt^(1/3)))
  }

  if(degree == 4){
    ## compute weighted moments up to fourth order
    mmt <- c(mmt, cokurtosis(dsc*wgt^(1/4)))
  }
  
  ## return moments and remove names
  return(mmt)
}

## names for moments (not used)
collapse_names <- function(y) {
  expand.grid(dimnames(y)) %>% 
    apply(1, function(y0) {
      t0 <- table(y0)
      paste0(names(t0), 
             ifelse(t0 > 1, paste0('^',t0), ''),
             collapse='*')
    })  
}

## logistic transform for optimization variables
logi  <- function(x, ymin=0, ymax=1)
  ymin + (ymax-ymin) / (1 + exp(-x))

## inverse logistic transform for optimization variables
ilogi <- function(y, ymin=0, ymax=1)
  -log((ymax-ymin) / (y - ymin) - 1) 


## Create variable with levels corresponding to numeric missingness patterns
missing_pattern <- function(dat) {
  
  if(is.data.frame(dat))
    dat <- as.matrix(dat)
  
  if(!is.numeric(dat))
    stop("'dat' must contain only numeric data")
  
  as.factor(apply(1-is.na(dat), 1, paste0, collapse=''))
  
}

## Create variable with levels corresponding to categorical missingness patterns
missing_pattern_cat <- function(dat) {
  
  if(is.data.frame(dat))
    dat <- as.matrix(dat)
  
  if(any(is.numeric(dat)))
    stop("'dat' must contain only categorical data")
  
  as.factor(apply(1-is.na(dat), 1, paste0, collapse=''))
}

## use the data sphere method to partition quantitative data
## with missing values in numeric variables
## dat    - a data frame with only numeric variables
## min_obs - minimum number of observations required to form two layers
## min_pyr - minimum number of observations required to form pyramids
## min_3lay - minimum number of observations required to form three layers
data_sphere_partition_miss <- function(dat, min_obs = 2, 
                                       min_pyr = 3, min_3lay = 3, 
                                       ignore_NA = FALSE) {
  
  if(nrow(dat) < min_obs){
    dat %<>% mutate(`(partition)` = "1")
    return(dat)
  }
  
  layers <- ifelse(nrow(dat) < min_3lay, 2, 3)
  
  wgt <- dat[,"weight", drop = TRUE]
  dat <- dat[,-which(colnames(dat) == "weight"), drop = FALSE]
  
  ## subset to non-missing numeric variables then scale all data 
  ## also require that variables have more than 1 unique value (not including NAs)
  dsc <- dat %>% 
    select_if(is.numeric) %>% 
    select_if(~n_distinct(.,na.rm = TRUE) > 1) %>%
    select_if(~sum(!is.na(.)) > 0) %>%
    as.matrix %>% 
    scale 
  
  which.max.na <- function(x){
    if(all(is.na(x)))
    # if(any(is.na(x)))
      return(NA)
    else
      return(which.max(x))
  }
  
  ## compute distances from center - for ALL observations
  ## distance from center is still known on observed axes
  dst <- sqrt(rowSums(dsc^2, na.rm = ignore_NA))
  
  ## compute distance quantiles for layers
  lev <- try(wtd.quantile(dst, probs=seq(1/layers, 1-1/layers, 1/layers),
                  weights = wgt, na.rm = TRUE))
  ## partition into layers
  ## these same layers will be used with missing values
  lay <- cut(dst, c(-Inf, lev, Inf)) %>% unclass
  
  ## if fewer than min_pyr obs, don't use pyramids
  if(nrow(dat) < min_pyr){
    prt <- paste(lay)
  } else{
    ## partition into pyramids
    pmx <- cbind(-dsc %>% pmax(0), dsc %>% pmax(0))
    pyr1 <- pmx %>% apply(1, which.max.na)
    
    ## partition into sub-pyramids
    ## replace maximum value of each row with 0
    pmx[cbind(1:nrow(pmx),pyr1)] <- 0
    ## identify index of second highest
    pyr2 <- pmx %>% apply(1, which.max.na)
    
    ## combine partition information
    prt <- 
      ifelse(lay == 1, paste(lay), 
             ifelse(lay == 2, paste(lay, pyr1, sep='.'),
                    paste(lay, pyr1, pyr2, sep='.'))) 
  }
  
  dat <- dat %>% mutate(`(partition)` = prt) %>% cbind(weight = wgt)
                        
  attr(dat, 'scaled:center') <- attr(dsc, 'scaled:center')
  attr(dat, 'scaled:scale') <- attr(dsc, 'scaled:scale')
  attr(dat, 'layer:breaks') <- lev 
  return(dat)
}


## Calculate the degree (i.e., highest order of moments) to be used
## Degree is calculated to return the lowest number of moments that is still
## greater than the total degrees of freedom (number of observations + weights)
calc_degree <- function(n, mn, p, all_mmt = TRUE){
  
  # table of weights/moments
  ummt <- data.frame(mmt = c("wgt","mn","vr","cvr","o3","o4"),
                     wgt = c(1000, 1000, 1000, 
                             1/(p*(p+1)/2-p),
                             1/(p*(p+1)*(p+2)/6),
                             1/(p*(p+1)*(p+2)*(p+3)/24)),
                     n = c(1,p,p,p*(p+1)/2-p,
                           p*(p+1)*(p+2)/6,
                           p*(p+1)*(p+2)*(p+3)/24))
  
  nu <- cumsum(ummt$n)
  
  # number of degrees of freedom (set approx = to number of pseudo points and weights)
  df <- mn*(p+1)
  uix <- ifelse(any(nu > df), which(nu > df)[1], length(nu)) # overdetermined moments
  if(uix <= 2) degree <- 1
  if(uix %in% c(3,4)) degree <- 2
  if(uix == 5) degree <- 3
  if(uix == 6) degree <- 4
  
  return(degree)
}

## Initialize squashed data set
## Values are created to have weights equal to the sum of weights in the original 
## data set. Weighted means are set to zero and weighted variances are set to 1.
## Iterated sampling from the original data is applied to ensure that a sufficient
## number of unique values are sampled before centering/scaling.
## Squashed initial values and corresponding min/max values are returned. 
initalize_squash <- function(dat, alpha){
 
 if(is.data.frame(dat))
  dat <- as.matrix(dat)
 
 wx <- dat[,ncol(dat)]
 sw <- sum(wx)
 mn <- reduced_sample_size(sw, alpha)
 p <- ncol(dat)-1
 df <- mn*(p+1)
 
 ## range of observed values
 rng <- apply(dat[,-ncol(dat), drop = FALSE], 2, range) %>%
  cbind('weight'=c(0,sw))
 
 ## vectors of min and max values
 ymn <- rep(rng[1,], rep(mn,p+1)) %>% matrix(mn)
 ymx <- rep(rng[2,], rep(mn,p+1)) %>% matrix(mn)
 
 # if only one squashed observation, return column means (0s)
 if(mn == 1){ 
  Y <- matrix(c(rep(0,ncol(dat)-1),sw), nrow = 1)
  colnames(Y) <- colnames(dat)
  return(list(init = Y, ymn = ymn, ymx = ymx))
 }
 
 eps <- 1e-3
 Y <- ymn-eps
 counter <- 0
 while(!(all(Y > ymn) & all(Y < ymx))){
  
  if(counter > 100) {
   # warning("Squashed matrix initialization failed. Check 'initialize_squash' function.") 
   
   Y[Y<ymn] <- ymn[Y<ymn] + 1e-3
   Y[Y>ymx] <- ymx[Y>ymx] - 1e-3
   
   break
  } else{
   
   counter <- counter + 1
   ## temporarily fill in values with column means before creating pseudo data
   dat_m <- na.aggregate(dat)
   
   # take sample from unique values - need 2 to calculate 
   dat_m <- dat_m[sample(nrow(dat_m), mn),,drop = FALSE]
   Y <- dat_m[,-ncol(dat_m), drop = FALSE]
   wy <- dat_m[,ncol(dat_m)]
   
   nonunique_row <- apply(Y, 2, function(y) length(unique(y)) <= 2)
   if(any(nonunique_row)){
    Y[,nonunique_row] <- Y[,nonunique_row] + rnorm(length(Y[,nonunique_row]), 
                                                   Y[,nonunique_row], sd = 1e-2)
   }
   
   # 1) scale weights
   wy <- wy * sum(wx) / sum(wy)
   
   # 2) subtract weighted mean to center
   wcen_y <- (rep(1,nrow(Y))%*%(wy*Y))[1,]
   Yc <- t.default(t.default(Y) - wcen_y/sum(wy))
   
   # if only one row, return centered values (0s)
   if(nrow(Yc) > 1){
    # 3) scale by wsd_x / wsd_y
    var_y <- colSums(wy*Yc^2)
    wsd_y <- sqrt(var_y / (sum(wy)-1))
    Ysc <- t(t(Yc) / wsd_y)
   } else{
    Ysc <- Yc
   }
   
   Y <- cbind(Ysc, wy)
  }
 }
 
 # check if values equal min/max - will return Inf during logit tranformation
 if(any(Y == ymn) | any(Y == ymx)){
  Y[Y==ymn] <- Y[Y==ymn] + 1e-3
  Y[Y==ymx] <- Y[Y==ymx] - 1e-3
 }
 
 colnames(Y) <- colnames(dat)
 
 return(list(init = Y, ymn = ymn, ymx = ymx))
}



## -----------------------------------------------------------------------------
## E-step functions ------------------------------------------------------------
## -----------------------------------------------------------------------------


## Function to expand a data set based on missingness in categorical values
##
## Each row with missing categorical variables is matched to fully-observed rows
## that have the most similar categorical variables based on the Gower metric. 
##
## Each row is expanded to have each observed combination of missing categorical 
## variables that were observed in the match.
##
## Each expansion receives weight equal to the observed proportion of times that
## the categorical combination appeared.
##
## dat - data frame with categorical and numeric variables, if present
expand_categorical <- function(dat){
  
  dat <- dat %>% group_by_if(~!is.numeric(.))
  gr <- attr(dat, "groups")
  # identify missingness patterns in categorical variables
  # used to ensure that info is borrowed from groups with observed variables
  mps <- missing_pattern_cat(dat[,!sapply(dat,is.numeric)])
  mps_names <- names(dat[,!sapply(dat,is.numeric)])
  
  for(mp in levels(mps)){
    miss_ix <- which(strsplit(mp,split = "")[[1]] == 0)
    
    if(length(miss_ix)>0){ # if any missing variables
      obs_mp <- sapply(setdiff(levels(mps),mp), function(x) {
        strsplit(x,split = "")[[1]][miss_ix] == 1
      })
      pat_obs <- which(mps %in% names(obs_mp))
      
      ## identify groups with shortest distance in categorical variable space
      keys_miss <- group_keys(dat[mps %in% mp,])
      keys_obs <- group_keys(dat[pat_obs,])
      
      ## distance between observed categorical variables
      dst <- gower.dist(as.data.frame(keys_miss), 
                        as.data.frame(keys_obs))
      
      ## indicies of obs_gr that are closest
      min_dst <- apply(dst, 1, function(x){
        rx <- rank(x)
        unname(which(rx == min(rx)))
      })
      rm(dst)
      
      dat_reconstruct <- vector("list", length(min_dst))
      for(i in 1:length(min_dst)){
        # need to match keys to observations
        # expand observations then merge
        
        ## keys from observed data that are closest to the ith missing pattern
        rows_imp <- unlist(merge(keys_obs[min_dst[[i]],],gr)[,".rows"])
        vars_imp <- dat[rows_imp,mps_names[miss_ix], drop = FALSE]
        
        ## impute joint values rather than marginal
        vals_imp <- apply(vars_imp, 1, paste, collapse = "|")
        weights_imp <- dat[rows_imp,"weight"]
        
        ## expand values to impute - weight by probability in group
        tbl <- as.data.frame(wtd.table(vals_imp, w = weights_imp))
        tbl$sum.of.weights <- tbl$sum.of.weights/sum(tbl$sum.of.weights)
        tbl <- cbind(data.frame(do.call('rbind', strsplit(as.character(tbl$x),'|',fixed=TRUE))),
                     tbl$sum.of.weights)
        names(tbl) <- c(names(vars_imp), "weight")
        
        ## merge with observations missing values
        rows_obs <- unlist(merge(keys_miss[i,],gr)[,".rows"])
        
        dat_reconstruct[[i]] <- cbind(
          as.data.frame(dat[rows_obs,][rep(seq_len(nrow(dat[rows_obs,])), each = nrow(tbl)),
                         setdiff(names(dat),names(tbl))]),
          as.data.frame(tbl[rep(seq_len(nrow(tbl)), times = length(rows_obs)),])
        )
        dat_reconstruct[[i]] <- dat_reconstruct[[i]][,setdiff(names(dat),"(partition)")]
      } # end iteration over i
      
      # replace rows in dat
      dat <- rbind(
        as.data.frame(dat[-which(mps == mp),-which(names(dat) == "(partition)")]), 
        do.call("rbind",dat_reconstruct)
        )
    } # end check if mp is missing
  } # end iteration over mps
  
  return(dat)
} 

## Apply expectation step to data sphere partition
##
## Data with missing values are partitioned by data_sphere_partition_miss() 
## based on fully observed values. Each cluster formed is assumed to be MVN 
## distributed, with means and variances calculated. For each observation with 
## missing values, the probability of inclusion in each cluster is calculated 
## based on the marginal density of observed values. A probability of "min_prob" 
## or larger is required for assignment. Probabilities are normalized to equal 1
## and observations are assigned to each cluster with duplicate copies made in 
## the data set.
##
## dat - data set
## ... - arguments passed to data_sphere_partition_miss() -- most likely the number
## of observations required to use pyramid/sub-pyramid partitions
## min_prob - minimum probability of belonging to a cluster required for assignment.
## clusters that match with less than min_prob are ignored.
## Estep -- If false, becomes a wrapper function for data_sphere_partition_miss()
data_sphere_partition_Estep <- function(dat, ..., min_prob = 0.05, Estep = FALSE){
  
  dat <- data_sphere_partition_miss(dat, ...)

  # if there aren't any missing partitions or Estep is false, return data frame
  if(all(!is.na(dat$`(partition)`)) | !Estep) return(dat)
  
  # if there are fewer than 2 partitions assign all to have the same value
  if(sum(!is.na(dat$`(partition)`)) < 2){
   dat$`(partition)` <- "1"
   return(dat)
  }
  
  fcov <- function(x,w){
    cov.wt(x = x[,-ncol(x), drop = FALSE], 
           wt = x[,ncol(x), drop = TRUE])
  }
  
  ## calculate means and covariances within each cluster, excluding 
  ## values with NAs (missing partition variable). 
  ## Need to subset to variables on which mvn probabilities can be calculated
  mis_ix <- which(is.na(dat$`(partition)`))
  wgt <- dat[,"weight"]
  prt <- dat[,"(partition)"]
  gr_dat <- dat[-mis_ix,] %>% 
    select_if(~ sum(!is.na(.)) > 0 & n_distinct(.) > 2) %>%
    mutate(weight = wgt[-mis_ix], `(partition)` = prt[-mis_ix]) %>%
    group_by(`(partition)`) %>%
    add_count() %>%
    filter(n>1) %>%
    select(-n)
  
  prts <- unlist(group_keys(gr_dat))
  gr_cov <- gr_dat %>% 
    group_map(~fcov(.x))
  rm(gr_dat)
  
  ## calculate probability of falling into each point
  nms <- colnames(gr_cov[[1]]$cov)
  wx <- unname(unlist(dat[mis_ix,"weight"]))
  group_probs <- matrix(apply(dat[mis_ix,nms], 1, function(x){
    obs_ix <- which(!is.na(x))
    gp <- sapply(gr_cov, function(clus){
      if(length(obs_ix) == 1){
        dnorm(unlist(x[obs_ix]), mean = clus$center[obs_ix], 
              sd = clus$cov[obs_ix,obs_ix])
      } else{
        dmvnorm(x[obs_ix], 
                mean = clus$center[obs_ix], 
                sigma = clus$cov[obs_ix,obs_ix]) 
      }
    })
    
    if(all(gp == 0)){
      ## if all are so unlikely that probs = 0, assign to largest category
      gp[which.max(sapply(gr_cov, `[[`, "n.obs"))] <- 1
    }
    ## normalize group probabilities & remove low probabilities
    gp <- gp / sum(gp)
    gp[gp < min_prob] <- 0
    gp
  }), ncol = length(mis_ix), nrow = length(gr_cov))
  
  # ## renormalize probabilities - each column is one observation
  group_probs <- t.default(group_probs) / colSums(group_probs) * wx
  # group_probs <- t.default(group_probs / colSums(group_probs) * wx)
  
  ## create data frame with all observations
  colnames(group_probs) <- paste0("part_",prts)
  new_obs <- cbind(dat[mis_ix,nms], group_probs)
  new_obs <- reshape(new_obs, 
                     direction = "long", 
                     varying = list(colnames(group_probs)),
                     v.names = "weight",
                     timevar = "(partition)",
                     times = gsub("part_", "", colnames(group_probs)))
  new_obs <- new_obs[new_obs$weight > 0,]
  dsm <- dat[mis_ix,]
  dsm$id <- 1:nrow(dsm)
  new_obs <- merge(dsm, new_obs, all.y = TRUE)
  new_obs <- new_obs[,-which(names(new_obs) == "id")]
  return(rbind.data.frame(dat[-mis_ix,], new_obs))
}


# gaussian mixture model clustering
# Assign number of clusters according to rule nclus = log(M,base=beta)
# Find a value of beta that appears to work well
# If not Estep: all variables will be either 
# Estep: 
# 1) Initially cluster all values before assigning categorical values using DS
# 2) Form clusters from all fully-observed observations
# 3) Assign observations with missing values to existing clusters
# 4) If no observations are fully-observed, form clusters on all obs and keep asignments


## Apply E-step to hyper-rectangle clustering method. Function is applied within
## data_hyper_rectangle()
## Regions are formed based on quantiles of observed values in each variable
## Observations with missing values are assigned to all sub-groups that match on
## the observed variables
##
## dat - data frame
## lay - layer variable created in data_hyper_rectangle()
Estep_hyper_rect <- function(dat, lay){
  
  na_ix <- rowSums(is.na(lay)) != 0
  ful_obs <- dat[-which(na_ix),]
  mis_obs <- dat[which(na_ix),]
  
  tprt <- table(dat$`(partition)`)
  lev <- unique(lay[na_ix,, drop = FALSE])
  lev_prt <- apply(lev, 1, paste, collapse = ".")
  
  new_obs <- lapply(1:nrow(lev), function(i){
    mix <- which(is.na(lev[i,]))
    nmatch <- ncol(lev) - length(mix)
    sub_ix <- which(rowSums(lay[,-mix,drop = FALSE] == rep(lev[i,-mix], 
                                                           each = nrow(lay))) 
                    == nmatch)
    sub_ix <- setdiff(sub_ix, which(na_ix == TRUE))
    if(length(mix) > 1){
      tab_ix <- lay[sub_ix,mix, drop = FALSE]
      cats <- dat$`(partition)`[sub_ix][complete.cases(tab_ix)]
      prbs <- prop.table(table(cats))
    }else{
      prbs <- prop.table(table(lay[sub_ix,mix], useNA = "no"))
    }
    
    ## reconstruct data frame
    grp <- paste(lev[i,], collapse = ".")
    nreps <- tprt[names(tprt) == grp]
    m <- mis_obs[mis_obs$`(partition)` == lev_prt[i],]
    m <- m[rep(seq_len(nrow(m)), each = length(prbs)),]
    prt_m <- matrix(rep(lev[i,], times = length(prbs)), byrow = TRUE, nrow = length(prbs))
    
    if(length(mix) > 1){
      prt_m[,mix] <- t(sapply(names(prbs), function(x) 
        as.numeric(strsplit(x[1], "\\.")[[1]])[mix]))
    } else{
      prt_m[,mix] <- as.integer(names(prbs))
    }
    
    m[,"(partition)"] <- rep(apply(prt_m, 1, paste, collapse = "."), 
                             times = nreps)
    m[,"weight"] <- rep(prbs, times = nreps) * m[,"weight"]
    m
  })
  dat_new <- rbind(ful_obs, do.call("rbind", new_obs))
  return(dat_new)
}

## partition data based on hyper-rectangle approach, with or without E-step
## dat - data frame
## p - percentiles of each variable at which to make splits
## Estep - Logical. If TRUE, observations with missing values will be assigned
## to all regions that match on observed values and weighted according to marginal
## probabilities in each group.
data_hyper_rectangle <- function(dat, p = c(0.25,0.75), Estep = TRUE) {
  
  wgt <- dat[,"weight",drop = TRUE]

  ## subset to numeric, non-missing, variables, with enough values to calculate
  ## percentiles
  dnm <- dat %>% 
    select(-weight) %>%
    select_if(is.numeric) %>% 
    select_if(~sum(!is.na(.)) > 0) %>%
    select_if(~n_distinct(.) > length(p)) %>% 
    as.matrix
  
  ## calculate boundaries based on weighted quantiles of each variable
  lay <- apply(dnm, 2, function(x){
    q <- wtd.quantile(x, probs = p, weights = wgt, na.rm = TRUE)
    unclass(cut(x,c(-Inf,q,Inf)))
  })
  
  ## create partitions
  dat$`(partition)` <- apply(lay, 1, paste, collapse = ".")
  
  ## if E-step, assign each obs with a NA partition to each of the 
  ## appropriate sub-partitions with weight equal to empirical probability
  if(Estep){
    return(Estep_hyper_rect(dat,lay))
  } else{
    return(dat)
  }
}

## Compute moments when observations are missing
## dat - matrix of numeric data
## degree - degree of approximation (i.e., the highest order of moments to match)
## boot - experimental, ignore for now. The idea is to get the squashed sample 
## to match the empirical variability in original data moments as well as the values
compute_moments_miss <- function(dat, degree, boot = FALSE) {
  
  wgt <- dat[,ncol(dat),drop = TRUE]
  dsc <- dat[,-ncol(dat), drop = FALSE]
  
  ## Order of moments:
  ## 0th, 1st, 2nd (pure), 2nd (mixed), 3rd, 4th
  ## expand, then impute, then sum
  p <- ncol(dsc)
  Mlist <- list(matrix(1:p, nrow = p), 
                rbind(cbind(1:p,1:p),
                      which(lower.tri(diag(rep(1,p))), 
                            arr.ind = TRUE)))
  
  if(degree >= 3){
    Mix <- matrix(0, nrow = p*(p+1)*(p+2)/6, ncol = 3)
    ix <- 0
    for(i in 1:p){
      for(j in i:p){
        for(k in j:p){
          ix <- ix + 1
          Mix[ix,] <- c(i,j,k)
        }
      }
    }
    Mlist <- c(Mlist, list(Mix))
  }
  
  if(degree == 4){
    Mix <- matrix(0, nrow = p*(p+1)*(p+2)*(p+3)/24, ncol = 4)
    ix <- 0
    for(i in 1:p){
      for(j in i:p){
        for(k in j:p){
          for(l in k:p){
            ix <- ix + 1
            Mix[ix,] <- c(i,j,k,l)
          }
        }
      }
    }
    Mlist <- c(Mlist, list(Mix))
  }
  
  calc_moment <- function(ix){
    ## values will be NA when any variable involved in moment is missing
    ## replace value with expectation of moment
    mt <- rowProds(dsc[,ix,drop = FALSE])
    mt[is.na(mt)] <- wtd.mean(mt, na.rm = TRUE, weights = wgt)
    sum(mt * wgt, na.rm = TRUE)
  }
  
  if(!boot){
    mmts <- sapply(1:length(Mlist), function(i){
      apply(Mlist[[i]], 1, calc_moment)
    })
  } else{
    ## Still being tested -- not ready for use
    ## calculate moments without summing over observations
    mmt_mat <- do.call("cbind",sapply(1:length(Mlist), function(i){
      apply(Mlist[[i]], 1, function(ix) rowProds(dsc[,ix,drop = FALSE]))
    }))
    
    ## resample observations within missingness patterns
    mp <- missing_pattern(mmt_mat)
    mmtB <- t.default(replicate(n = 100, sample_moments(mmt_mat, wgt, mp)))
    mmts <- svd_mmt(mmtB,10)
  }
  
  return(c(sum(wgt), unlist(mmts)))
}

## Function to impute sample moments within missingness patterns (mp)
## Experimental - not being used
sample_moments <- function(mmts, wgt, mp){
  # identify missingness patterns
  for(p in levels(mp)){
    na_cols <- is.na(colSums(mmts[mp == p,,drop =FALSE]))
    cc <- complete.cases(mmts[,na_cols])
    tmp <- mmts[cc,na_cols]
    mmts[mp == p,na_cols] <- tmp[sample(1:nrow(tmp), sum(mp == p), 
                                        replace = TRUE, prob = wgt[cc]),]
  }
  return(colSums(mmts * wgt))
}

## Perform svd on moments and project onto lower level
## Experimental - not being used
svd_mmt <- function(mmts,ndim=1){
  sv <- svd(t.default(t.default(mmts) - colMeans(mmts)))
  colMeans(t.default(t.default(sv$v[,1:ndim,drop =FALSE]) %*% 
                       t.default(mmts)) %*% t.default(sv$v[,1:ndim,drop =FALSE]))
}


## Gradient for objective function
## init - initialized squash values (ilogi transformed)
## ymn - minimum values for squashed data
## ymx - maximum values for squashed data
## mn - number of rows in squashed data
## degree - maximum order of moments matched
## mmt_fn - function to calculate moments -- not used by the gradient, but 
## included for nlm() so that fn and grd have the same arguments 
## mmt - moments from original data sample
## u - weights indicating priority of matching each moment
grd <- function(init, ymn, ymx, mn, degree, mmt_fn, mmt, u) {
  
  mmt <- unname(mmt)
  ## reconstruct data
  dat_m <- matrix(logi(init, ymn, ymx), nrow=mn)
  w <- dat_m[,ncol(dat_m)]
  Y <- dat_m[,-ncol(dat_m), drop = FALSE]
  
  # gradient with respect to transformation
  init <- matrix(init, nrow = mn)
  g.tr <- sapply(1:ncol(init), function(j){
   (ymx[,j] - ymn[,j]) / (2*(1+cosh(init[,j])))
  })
  
  p <- ncol(init)-1
  vc <- c(1,p,p,p*(p+1)/2-p)
  if(degree >= 3) vc <- c(vc, p*(p+1)*(p+2)/6)
  if(degree == 4) vc <- c(vc, p*(p+1)*(p+2)*(p+3)/24)
  
  zl <- ul <- vector("list", length(vc))
  zl[vc>0] <- split(mmt, rep(1:(degree+2), vc))
  ul[vc>0] <- split(u, rep(1:(degree+2), vc))
  
  # 0th order moment
  gw <- rep(-2*ul[[1]]*(zl[[1]]-sum(w)), length(w))
  gy <- matrix(0,mn,p)
  
  # first and (pure) second order moments
  for(j in 1:p){
    pwy <- c(crossprod(w,Y[,j]))
    pwy2 <- c(crossprod(w,Y[,j]^2))
    t1 <- 2*ul[[2]][j]*(zl[[2]][j]-pwy)
    t2 <- 2*ul[[3]][j]*(zl[[3]][j]-pwy2)
    gw <- gw - t1*Y[,j] - t2*Y[,j]^2
    gy[,j] <-  gy[,j] - t1*w -t2*2*w*Y[,j]
  }
  
  # second order cross moments
  mo <- which(lower.tri(diag(rep(1,p))), arr.ind = TRUE)
  if(nrow(mo)>0){
    for(l in 1:nrow(mo)){
      yjk <- Y[,mo[l,1]]*Y[,mo[l,2]]
      gw <- gw - 2*ul[[4]][l]*(zl[[4]][l]-c(crossprod(w,yjk)))*yjk
      xx <- -2*ul[[4]][l]*(zl[[4]][l]- c(crossprod(w*Y[,mo[l,1]],Y[,mo[l,2]])))
      gy[,mo[l,1]] <- gy[,mo[l,1]] + xx*Y[,mo[l,2]]*w
      gy[,mo[l,2]] <- gy[,mo[l,2]] + xx*Y[,mo[l,1]]*w
    }
  }
  
  # third order moments
  if(degree >= 3){
    Mix <- matrix(0, nrow = vc[5], ncol = 3)
    ix <- 0
    for(i in 1:p){
      for(j in i:p){
        for(k in j:p){
          ix <- ix + 1
          Mix[ix,] <- c(i,j,k)
        }
      }
    }
    
    for(ii in 1:nrow(Mix)){
      smii <- -2*ul[[5]][ii]*(zl[[5]][ii] - c(crossprod(w*Y[,Mix[ii,1]],Y[,Mix[ii,2]]*Y[,Mix[ii,3]])))
      gw <- gw + smii*Y[,Mix[ii,1]]*Y[,Mix[ii,2]]*Y[,Mix[ii,3]]
      smiiw <- smii*w
      tmix <- tabulate(Mix[ii,], nbins = ncol(Y))
      if(any(tmix == 3)){
        gy[,Mix[ii,1]] <- gy[,Mix[ii,1]] + smiiw*3*Y[,Mix[ii,1]]^2
      } else if(any(tmix == 2)){
        tmix1 <- which(tmix == 1)
        tmix2 <- which(tmix == 2)
        gy[,tmix2] <- gy[,tmix2] + smiiw*2*Y[,tmix2]*Y[,tmix1]
        gy[,tmix1] <- gy[,tmix1] + smiiw*Y[,tmix2]^2
      } else{
        gy[,Mix[ii,1]] <- gy[,Mix[ii,1]] + smiiw*Y[,Mix[ii,2]]*Y[,Mix[ii,3]]
        gy[,Mix[ii,2]] <- gy[,Mix[ii,2]] + smiiw*Y[,Mix[ii,1]]*Y[,Mix[ii,3]]
        gy[,Mix[ii,3]] <- gy[,Mix[ii,3]] + smiiw*Y[,Mix[ii,1]]*Y[,Mix[ii,2]]
      }
    }
  }
  
  # fourth order moments
  if(degree == 4){
    Mix <- matrix(0, nrow = vc[6], ncol = 4)
    ix <- 0
    for(i in 1:p){
      for(j in i:p){
        for(k in j:p){
          for(l in k:p){
            ix <- ix + 1
            Mix[ix,] <- c(i,j,k,l)
          }
        }
      }
    }
    
    for(ii in 1:nrow(Mix)){
      smii <- -2*ul[[6]][ii]*(zl[[6]][ii] - c(crossprod(w*Y[,Mix[ii,1]]*Y[,Mix[ii,2]],Y[,Mix[ii,3]]*Y[,Mix[ii,4]])))
      gw <- gw + smii*Y[,Mix[ii,1]]*Y[,Mix[ii,2]]*Y[,Mix[ii,3]]*Y[,Mix[ii,4]]
      smiiw <- smii*w
      
      tmix <- tabulate(Mix[ii,], nbins = ncol(Y))
      if(any(tmix == 4)){
        gy[,Mix[ii,1]] <- gy[,Mix[ii,1]] + smiiw*4*Y[,Mix[ii,1]]^3
      } else if(any(tmix == 3)){
        tmix1 <- which(tmix == 1)
        tmix3 <- which(tmix == 3)
        gy[,tmix3] <- gy[,tmix3] + smiiw*3*Y[,tmix3]^2*Y[,tmix1]
        gy[,tmix1] <- gy[,tmix1] + smiiw*Y[,tmix3]^3
      } else if(sum(tmix==2)==2){
        ij <- which(tmix == 2)
        gy[,ij[1]] <- gy[,ij[1]] + smiiw*2*Y[,ij[2]]^2*Y[,ij[1]]
        gy[,ij[2]] <- gy[,ij[2]] + smiiw*2*Y[,ij[1]]^2*Y[,ij[2]]
      }else{
        gy[,Mix[ii,1]] <- gy[,Mix[ii,1]] + smiiw*Y[,Mix[ii,2]]*Y[,Mix[ii,3]]*Y[,Mix[ii,4]]
        gy[,Mix[ii,2]] <- gy[,Mix[ii,2]] + smiiw*Y[,Mix[ii,1]]*Y[,Mix[ii,3]]*Y[,Mix[ii,4]]
        gy[,Mix[ii,3]] <- gy[,Mix[ii,3]] + smiiw*Y[,Mix[ii,1]]*Y[,Mix[ii,2]]*Y[,Mix[ii,4]]
        gy[,Mix[ii,4]] <- gy[,Mix[ii,4]] + smiiw*Y[,Mix[ii,1]]*Y[,Mix[ii,2]]*Y[,Mix[ii,3]]
      }
    }
  }
  
  out <- cbind(gy,gw) * g.tr
  # out <- cbind(gy,gw)
  return(unname(out))
}


## squash is a generic function
squash <- function(obj, ...)
  UseMethod('squash', obj)


## squash numeric data matrix (i.e., for an individual partition)
## dat   - numeric matrix
## alpha - degree of squashing (see 'reduced_sample_size') 
## maxit - maximum number of iterations for nlm
## ...   - arguments passed to 'nlm'
squash.matrix <- function(dat, alpha=1, maxit = 10000, degree = NULL, ...) {
  
  if(!is.numeric(dat))
    stop("'dat' must be a numeric matrix")
  
  ## return dat if only one observation in group
  if(nrow(dat) == 1) 
    return(dat)
  
  ## save original names to reference later
  colnm_dat <- colnames(dat)
  
  # 1. center/scale X
  wx <- dat[,ncol(dat)]
  swx <- sum(wx)
  dat <- dat[,-ncol(dat), drop = FALSE]
  
  ## if N=2, M=2 also -- just return original observations
  if(min(colSums(!is.na(dat))) < 2){
    # out <- matrix(c(colMeans(dat,na.rm = TRUE),swx), nrow = 1)
    ## NAs won't be present during propagation squashing
    out <- cbind(na.aggregate(dat),wx)
    colnames(out) <- colnm_dat
    return(out)
  }
  
  if(any(colSums((!is.na(dat))*1*wx) < 2)){
    return(matrix(c(colMeans(dat,na.rm = TRUE),swx), nrow = 1,
                  dimnames = list(NULL, colnm_dat)))
  }
  
  ## remove columns for which all observations are constant -- added back later
  one_unique_obs <- apply(dat, 2, function(x){
    length(unique(x[!is.na(x)])) == 1
  })
  
  if(any(one_unique_obs)){
    nms_orig <- c(colnames(dat),"weight")
    Xconst <- dat[,which(one_unique_obs),drop = FALSE]
    dat <- dat[,-which(one_unique_obs)]
  }
  
  if(any(is.na(dat))){
    wmu_x <- apply(dat, 2, wtd.mean, weights = wx)
    Xc <- t.default(t.default(dat)-wmu_x)
    wsds_x <- sqrt(apply(Xc, 2, wtd.var, weights = wx))
  } else{
    wcen_x <- (rep(1,nrow(dat))%*%(wx*dat))[1,]
    wmu_x <- wcen_x/swx
    Xc <- t.default(t.default(dat)- wmu_x)
    cvnc <- crossprod(Xc*sqrt(wx))
    wsds_x <- sqrt(diag(cvnc) / (swx-1))
  }
  
  Xsc <- t.default(t.default(Xc) / wsds_x)
  
  # 2. create matrix of power vectors
  p <- ncol(Xsc)
  mn <- reduced_sample_size(swx, alpha)
  if(any(is.na(Xsc))){
    degree <- calc_degree(n = nrow(Xsc),mn,length(colnm_dat)-1, all = TRUE)
  } else{
    degree <- calc_degree(n = swx,mn,length(colnm_dat)-1, all = TRUE)
  }
  
  # 3. initialize squashed matrix
  sqi <- initalize_squash(cbind(Xsc, wx), alpha = alpha)
  
  # 4. calculate moments for full data
  if(any(is.na(Xsc))){
    mmt <- compute_moments_miss(cbind(Xsc, wx), degree = degree)
  } else{
    mmt <- compute_moments(cbind(Xsc, wx), degree = degree)
  }
  
  ## weights for obj. fun; means and vars get priority
  u <- c(1000, rep(1000, p), rep(1000, p), # weights, means, variances
         rep(1/(p*(p+1)/2-p), p*(p+1)/2-p)) # covariances
  
  if(degree >= 3){
    u <- c(u, rep(1/(p*(p+1)*(p+2)/6), 
                  p*(p+1)*(p+2)/6))
  }
  if(degree >= 4){
    u <- c(u, rep(1/(p*(p+1)*(p+2)*(p+3)/24), 
                  p*(p+1)*(p+2)*(p+3)/24))
  }
  
  fn <- function(init, ymn, ymx, mn, degree, mmt_fn, mmt, u) {
    
    ## reconstruct data - init is logit transformed
    dat_m <- matrix(logi(init, ymn, ymx), nrow=mn)
    
    ## compute moments for reduced data
    mmt_m <- mmt_fn(dat_m, degree = degree)
    
    ## weighted sum of squares for moments
    out <- sum2(u * (mmt - mmt_m)^2)
    attr(out, "gradient") <- grd(init, ymn, ymx, mn, degree, mmt_fn, mmt, u)
    out
  }
  
  if(nrow(sqi$init) == 1){ # if only one observation, doesn't need to be optimized
   dat_m <- sqi$init
  } else{
   ## transform to logit scale for unbounded optimization
   logitp <- ilogi(sqi$init, sqi$ymn, sqi$ymx)
   
    opt <- try(nlm(f = fn, p = logitp, 
                   ymn = sqi$ymn, ymx = sqi$ymx,
                   mn=mn, degree = degree, mmt_fn = compute_moments, mmt = mmt, u=u,
                   iterlim = maxit, check.analyticals = FALSE,
                   steptol = 1e-8, gradtol = 1e-8, print.level = 0, ...))
    
    dat_m <- logi(opt$estimate, sqi$ymn, sqi$ymx)
  }
  dat_m[,-ncol(dat_m)] <- t(t(dat_m[,-ncol(dat_m)])*wsds_x + wmu_x)
  colnames(dat_m) <- c(colnames(Xsc),"weight")
  
  ## add back any constant columns in correct order
  if(any(one_unique_obs)){
    xvals <- apply(Xconst, 2, function(x){unique(x[!is.na(x)])})
    col_add <- matrix(rep(xvals, nrow(dat_m)), nrow = nrow(dat_m), byrow = TRUE, 
                      dimnames = list(NULL, colnames(Xconst)))
    dat_m <- cbind(dat_m,col_add)[,nms_orig]
  }
  
  return(dat_m)
}

# group_modify function that allows for parallel processing
group_modify_cl <- function(df, fn, cl, ...){
  
  keys <- group_keys(df)
  df <- df %<>% group_split(.keep = FALSE)
  
  if(is.null(cl)){
    do.call("rbind", lapply(1:length(df), function(i){
      fni <- fn(df[[i]], ...)
      return(merge(keys[i,], fni))
    }))
  } else{
    dfm <- foreach(dfi=df) %dopar% {
      fn(dfi, ...)
    }
    do.call("rbind", lapply(1:length(dfm), function(i){
      merge(keys[i,], dfm[[i]])
    }))
  }
}

## Function to borrow values from nearby clusters when a cluster is formed with
## no observed values on a given variable. Only used during e-squashing
borrow_x <- function(dat){
  
  print("Borrowing information from nearby clusters")
  ## dat should be grouped by categorical levels
  keys <- group_keys(dat)
  
  ## groups with all x missing after Estep
  miss_gr <- which(sapply(group_split(dat, .keep = FALSE), 
                          function(x) any(colSums(is.na(x)) == nrow(x))))
  obs_gr <- setdiff(1:nrow(keys), miss_gr)
  
  ## calculate distance between categorical levels
  ## subset to only consider fully observed groups
  ## rows are missing, columns are observed
  dst <- gower.dist(as.data.frame(keys[miss_gr,]), 
                    as.data.frame(keys[obs_gr,]))
  ## indicies of obs_gr that are closest
  min_dst <- apply(dst, 1, function(x){
    rx <- rank(x)
    unname(which(rx == min(rx)))
  })
  
  ## sample missing x from each of these 
  for(i in 1:length(miss_gr)){
    key_nms <- which(names(dat) %in% names(keys))
    ## observations to be imputed -- miss_gr[i] says which group is to be used
    gri <- dat[attr(dat, "groups")$.rows[[miss_gr[i]]],-key_nms]
    ## which observed groups minimize the ith distance 
    imp_ix <- obs_gr[min_dst[[i]]]
    gr_imp <- dat[unlist(attr(dat, "groups")$.rows[imp_ix]),-key_nms]
    
    ## sample from joint distribution when possible
    miss_ix <- which(colSums(is.na(gri)) == nrow(gri))
    if(any(rowSums(is.na(gr_imp[,miss_ix])) == 0)){
      gr_imp <- gr_imp[rowSums(is.na(gr_imp[,miss_ix])) == 0,]
      ## impute values from gr_imp -- still possible that missing values exist
      gri[,miss_ix] <- gr_imp[sample(x = nrow(gr_imp), size = nrow(gri), 
                                     replace = TRUE), miss_ix]
    } else{
      for(mix in miss_ix){
        var_impi <- gr_imp[!is.na(gr_imp[,mix]),mix,drop=TRUE]
        gri[,mix] <- var_impi[sample(x = length(var_impi), size = nrow(gri), 
                                     replace = TRUE)]
      }
    }
    
    dat[attr(dat, "groups")$.rows[[miss_gr[i]]],-key_nms] <- gri
  }
  
  return(dat)
}

## squash data frame with partitioning
## dat    - data frame (with possibly categorical variables)
## alpha  - degree of squashing (see 'reduced_sample_size') 
## degree - maximum order of moments. If NULL, will match to 
## the lowest order moments such that the number of moments 
## is greater than the degrees of freedom (number of squashed
## points + weights). Can be specified to be lower if higher 
## order moments aren't required.
## cluster_numeric - Should numeric variables be clustered. Defaults to TRUE
## cl - cluster object for parallel processing. Used in numeric clustering
## and when squashing data.
## Estep - Logical. Should e-squashing be used instead of p-squashing, when
## missing values are present?
## cluster_method - "DS" = data sphere, "HR" = hyper rectantle
## ignore_NA - should NAs be ignored when applying cluster_method. If true,
## observations with NAs are grouped based on observed values. Only set to TRUE
## when clustering numeric variables prior to expanding categorical in E-step.
## lib-loc - location of libraries. For some reason, required for using packages with
## compiled functions (i.e., PerformanceAnalytics) in parallel

squash.data.frame <- function(dat, alpha=1, degree = NULL, 
                              cluster_numeric = TRUE, cl = NULL, 
                              miss_method = c("PSQ","ESQ"),
                              cluster_method = c("DS","HR"), 
                              ignore_NA = FALSE,
                              lib.loc = .libPaths()) {
 
  ## load packages locally
  packages_loaded <- (.packages())
  packages_required <- c("magrittr", # %>% operator
                         "dplyr", # several functions
                         "Hmisc", # wtd.mean, wtd.var, wtd.quantile fun
                         "matrixStats", # rowProds in compute_moments_miss()
                         "zoo", # na.aggregate in initalize_squash()
                         "mvtnorm", # dmvnorm in data_sphere_partition_Estep()
                         "PerformanceAnalytics", # used for 3rd/4th order moments
                         "StatMatch") # used for Gower metric between categorical variables
  lapply(setdiff(packages_required, packages_loaded), 
         require, character.only = TRUE)
  
  packages_loaded <- (.packages())
  if(any(setdiff(packages_required, packages_loaded))){
   package_diff <- paste(setdiff(packages_required, packages_loaded), collapse = ", ")
   stop(paste("The following packages must be installed:",package_diff))
  }
   
  if(!is.null(cl)){
    ## export functions and libraries to cluster
    fun_loaded <- clusterEvalQ(cl, ls())[[1]]
    fun_req <- c("squash.matrix","reduced_sample_size",
                 "logi","ilogi","squash","calc_degree",
                 "initalize_squash","compute_moments","compute_moments_miss",
                 "coskew","cokurtosis","grd","data_sphere_partition_miss",
                 "Estep_hyper_rect")
    clusterExport(cl, setdiff(fun_req, fun_loaded))
    clusterExport(cl, "lib.loc", envir = environment())
    
    ## export libraries
    clusterEvalQ(cl = cl, {
      library(magrittr)
      library(dplyr)
      library(Hmisc)
      library(matrixStats)
      library(PerformanceAnalytics, lib.loc = lib.loc)
      library(zoo)
      library(mvtnorm)
      library(StatMatch)
    })
  }
  
  miss_method <- match.arg(miss_method)
  Estep <- ifelse(any(is.na(dat)) & miss_method == "ESQ", TRUE, FALSE)
  cluster_method <- match.arg(cluster_method)
  
  ## check if any columns are missing all observations and drop
  if(any(apply(dat, 2, function(x) all(is.na(x))))){
    vars_miss <- names(dat)[apply(dat, 2, function(x) all(is.na(x)))]
    warning(paste("Some variables are entirely missing and are being dropped:", 
                  paste(vars_miss, collapse = ", ")))
    dat <- dat[,-which(names(dat) %in% vars_miss)]
  }
  
  ## if any missing numeric data, create missing pattern
  if(any(is.na(dat[,sapply(dat,is.numeric)])) & !Estep){
    print("Adding missingness patterns")
    dat %<>% mutate('(missing)' = missing_pattern(dat[,sapply(dat,is.numeric)])) 
  }
  
  ## add weights if not present
  if(!("weights" %in% names(dat))) dat[,'weight'] <- 1
  
  ## Estep for categorical variables
  if(Estep & any(is.na(dat[,!sapply(dat,is.numeric)]))){
    print("Expanding missing categorical variables")
    sw <- sum(dat$weight)
    dat <- expand_categorical(
      data_sphere_partition_miss(dat, ignore_NA = TRUE)
      )
    if(abs(sum(dat$weight) - sw) > 1e-3) stop("Weights are unequal")
  } 
  
  ## cluster numeric
  if(cluster_numeric){
    print("Clustering numeric variables")
    if(cluster_method == "DS"){
      dat %<>% group_by_if(~!is.numeric(.)) %>%
        group_modify_cl(fn = data_sphere_partition_Estep, 
                        cl = cl,
                        Estep = Estep,
                        ignore_NA = ignore_NA) %>%
        group_by_if(~!is.numeric(.))
    } else{
      dat %<>% group_by_if(~!is.numeric(.)) %>% 
        group_modify_cl(fn = data_hyper_rectangle, cl = cl, 
                        keep = TRUE, Estep = Estep) %>%
        group_by_if(~!is.numeric(.))
    }
  } else{
    dat %<>% group_by_if(~!is.numeric(.))
  }
  
  ## borrow information from nearby clusters if necessary
  miss_gr <- which(sapply(group_split(dat, .keep = FALSE), 
                          function(x) any(colSums(is.na(x)) == nrow(x))))
  if(Estep & length(miss_gr)>0){
    dat <- borrow_x(dat)
  }
  
  ## squash numeric data by group
  grfn <- function(x,y){
    ## remove columns with all missing before squashing
    ## remove columns with only one unique observation
    wgt <- x %>% select(weight)
    X <- x %>% select(-weight)
    mis_obs <- X %>% select_if(~all(is.na(.)) | n_distinct(.) == 1)
    if(ncol(mis_obs) > 0){
      mis <-  mis_obs %>% distinct() 
    }
    obs <- X %>% 
      select_if(~(!all(is.na(.)) & n_distinct(.) > 1)) %>%
      cbind(weight = wgt)
    
    if(ncol(obs) == 1){
      # if all observations are missing, sum weights and return NAs
      squ <- as_tibble(t(colSums(x)))
    } else{
      ## squash numeric data
      squ <- as.data.frame(squash(as.matrix(obs), alpha = alpha, degree = degree))
    }

    if(exists("mis")){
      merge(squ, mis) %>%
        select(names(x), 'weight')
    } else{
      squ %>% select(names(x), "weight")
    }
  }
  
  ## function to extract single group from grouped data frame
  group_extract <- function(dat,ix,keys){
    colnm <- setdiff(names(dat), names(keys))
    dat[attr(dat, "groups")$.rows[[ix]],colnm]
  }
  
  ## squash numeric data by group
  if(is.null(cl)){
    print("Squashing data")
    dat_m <- group_modify(dat, grfn)
    dat_m <- dat_m[,setdiff(names(dat_m), c("(missing)","(partition)"))]
    return(ungroup(dat_m))
  } else{
    print("Squashing data in parallel")
    keys <- group_keys(dat)
    dat_m <- foreach(dati = group_split(dat, .keep = FALSE), 
                      .errorhandling = "pass") %dopar% {
                        return(grfn(dati))
                      }
    dat_m <- lapply(1:length(dat_m), function(i){
     merge(keys[i,setdiff(names(keys), c("(missing)","(partition)"))],
           dat_m[[i]])
    })
    
    out <- try(do.call("rbind", dat_m))
    if(class(out) == "try-error") out <- dat_m
  }
  
  return(out)
}



