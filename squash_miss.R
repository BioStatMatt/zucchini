## Additional functions for extending data squashing to datasets with 
## missing values. 

library('dplyr')
library('magrittr')
library('gdata')


## use the data sphere method to partition quantitative data
## with missing values in numeric variables
## dat    - a data frame with only numeric variables
## layers - number of layers in partition
data_sphere_partition_miss <- function(dat, layers=2) {
 
 if(!all(sapply(dat, is.numeric)))
   stop("'dat' may only contain numeric data")
 
 ## subset to numeric variables then scale all data 
 dsc <- dat %>% 
  select_if(is.numeric) %>% 
  as.matrix %>% 
  scale 
 
 ## and compute distances from center
 dst <- dsc %>% `^`(2) %>% rowSums %>% sqrt
 
 ## compute distance quantiles for layers
 lev <- quantile(dst, probs=seq(1/layers, 1-1/layers, 1/layers),
                 na.rm = TRUE)
 
 ## partition into layers
 ## these same layers will be used with missing values
 lay <- cut(dst, c(-Inf, lev, Inf)) %>% unclass
 
 ## partition into pyramids
 ## -dsc %>% pmax(0) extracts the negative values
 ## of dsc and replaces positive values with 0
 ## dsc %>% pmax(0) extracts the positive values
 pmx <- cbind(-dsc %>% pmax(0), dsc %>% pmax(0))
 
 ## pyr1 provides the longest scaled distance from 0 
 ## of the numeric variables in each row.
 pyr1 <- pmx %>% apply(1, which.max)
 
 ## partition into sub-pyramids
 ## replace maximum value of each row with 0
 pmx[cbind(1:nrow(pmx),pyr1)] <- 0
 ## identify index of second highest
 pyr2 <- pmx %>% apply(1, which.max)
 
 ## combine partition information
 prt <- 
  ifelse(lay == 1, paste(lay), 
         ifelse(lay == 2, paste(lay, pyr1, sep='.'),
                paste(lay, pyr1, pyr2, sep='.')))
 
 dat <- dat %>% mutate(`(partition)` = prt)
 attr(dat, 'scaled:center') <- attr(dsc, 'scaled:center')
 attr(dat, 'scaled:scale') <- attr(dsc, 'scaled:scale')
 attr(dat, 'layer:breaks') <- lev 
 return(dat)
}


## Functions to return unique elements from coskew and cokurtosis matrices
## Adapted from M3.MM and M4.MM functions in PerformanceAnalytics package
## Takes in a pre-centered matrix, Xc
coskew <- function(Xc, mu, unbiased = FALSE, as.mat = FALSE) 
{
 NN <- NROW(Xc)
 PP <- NCOL(Xc)
 CC <- 1
 M3 <- .Call("M3sample", Xc, NN, PP, CC, PACKAGE = "PerformanceAnalytics")
 return(M3)
}

cokurtosis <- function(Xc, mu, as.mat = FALSE) 
{
 NN <- 1
 PP <- NCOL(Xc)
 M4 <- .Call("M4sample", Xc, NN, PP, PACKAGE = "PerformanceAnalytics")
 return(M4)
}



## Compute moments of a numeric data frame
## Similar as original, but with option to specify order up to order = 4.
## Also only returns unique elements of covariance matrix, rather than
## all elements. This function does not evaluate the E-step for missing values.
compute_moments <- function(dat, order = 2, ...) {
 
 if(order > 4 | order < 2) stop("The order must be between 2 and 4.")
 
 ## extract weights (last column)
 wgt <- dat[,ncol(dat)]
 dsc <- dat[,-ncol(dat)]
 
 cen <- (rep(1,nrow(dsc))%*%(wgt*dsc))[1,]
 dsc <- t.default(t.default(dsc)- cen/sum(wgt))
 
 # ## center and scale with weights
 # dsc <- corpcor::wt.scale(dsc, w = wgt, center = TRUE, scale = TRUE)
 # 
 # # means 
 # cen <- attr(dsc,"scaled:center")*sum(wgt)
 # 
 # # sd
 # sds <- attr(dsc,"scaled:scale")
 # 
 # # variances
 # vnc <- sds^2 * (sum(wgt)-1)
 # 
 # # covariances
 # cvnc <- crossprod(dsc*sqrt(wgt))
 
 cvnc <- crossprod(dsc*sqrt(wgt))
 
 ## compute weighted moments up to second order
 mmt <- c(sum(wgt), cen, diag(cvnc), cvnc[lower.tri(cvnc)])
 
 if(order >= 3){
  ## compute weighted moments up to third order
  mmt <- c(mmt, coskew(dsc*wgt^(1/3), mu = cen, as.mat = FALSE))
 }
 
 if(order == 4){
  ## compute weighted moments up to fourth order
  X <- dsc*wgt^(1/4)
  mmt <- c(mmt, cokurtosis(X, mu = cen, as.mat = FALSE))
 }
 
 ## return moments and remove names
 return(mmt)
}



## Work in progress.
## Compute Dth order moments for specified data with missing values.
## This function will apply the E-step to missing values by imputing
## the mean of each moment if imp_meth = "mean".
## It is significantly slower than compute_moments, but will only need
## to be run once on the original dataset.
compute_moments_miss <- function(dat,
                                 D = 2,
                                 imp_meth = c("mean","1hot"),
                                 ...) {
 
 imp_meth <- match.arg(imp_meth)
 
 ## extract weights (last column)
 wgt <- dat[,ncol(dat)]
 dsc <- dat[,-ncol(dat)]
 
 ## compute weighted sums (for weighted mean)
 ## The weighted sums exclude NA values and need to
 ## be scaled by 1/proportion observed
 
 nvec <- nrow(dsc)
 mvec <- try(colSums(!is.na(dsc)))
 # cen <- colSums(wgt*dsc, na.rm = TRUE) * nvec / mvec
 cen <- colSums(wgt*dsc, na.rm = TRUE)
 
 ## center
 ## Note: each column can have different numbers of observations
 mns <- apply(dsc, 2, Hmisc::wtd.mean, weights = wgt)
 dsc <- t.default(t.default(dsc)-mns)
 
 # need to expand columns into all cross-moments of order d <= D
 # length of expansion
 q <- ncol(dsc)
 L <- sum(is.na(colSums(dsc))) # number with missing values
 R <- sum(sapply(1:D, function(d) choose(d+q-1,q-1)))
 
 # enumerate distribution of powers to q boxes
 # need an R by q matrix
 M <- expand.grid(replicate(q, 0:D, simplify = FALSE))
 rsm <- rowSums(M)
 # central moments have already been calculated
 M <- as.matrix(M[rsm > 1 & rsm <= D,])
 
 # compute higher order moments
 # dsc[is.na(dsc)] <- 0
 
 vcv <- sapply(1:nrow(M), function(i){
  vec <- matrixStats::colProds(t.default(dsc) ^ M[i,])
  
  if(any(is.na(vec))){
   if(imp_meth == "mean"){
    # replace missing values with expected value
    vec[is.na(vec)] <- mean(vec, na.rm = TRUE)
   }
   
   if(imp_meth == "1hot"){
    # hot-deck imputation
    vec[is.na(vec)] <- sample(vec[!is.na(vec)], sum(is.na(vec)))
   }
  }
  
  sum(vec*wgt)
 })
 
 vcv_mat <- matrix(0, q, q)
 gdata::lowerTriangle(vcv_mat, diag = TRUE, byrow = TRUE) <- vcv
 gdata::upperTriangle(vcv_mat) <- gdata::lowerTriangle(vcv_mat, byrow = TRUE)
 
 ## return moments and remove names
 mmt <- c(sum(wgt), cen, vcv_mat)
 return(mmt)
}


## E-step for categorical variables. 
## Procedure: identify observations with missing categorical variables.
## Calculate probability of each possible value based on 1) observed proportions
## 2) multinomial model predictions fit to the full dataset with mean imputation,
## 3) multinomial model fit to only the fully observed variables.
## Create new observations with imputed values and weights equal to predicted 
## probability. Regroup dataset.
## Currently only works with one missing categorical variable -- needs to be extended.
## datgr: grouped data frame
Estep_cat <- function(datgr, sqwgt = NULL, method = c("prop","full_obs","mean_imp")){
 
 method <- match.arg(method)
 if(is.null(sqwgt)) sqwgt <- rep(1, nrow(datgr))
 
 # identify observations with missing categorical variables
 gr <- attr(datgr, "groups")
 gr_miss <- which(is.na(gr$a))
 id_miss <- lapply(gr_miss, function(x) gr$.rows[[x]])
 nmiss <- length(unlist(id_miss))
 obs_miss <- datgr[unlist(id_miss),]
 numvars <- sapply(datgr, is.numeric)
 
 # build a multinomial model to predict missing categories
 # if NAs exist in the continuous variables then it will 
 # predict NAs in the outcome.
 # options: 
 # 1. Calculate probabilities from raw proportions (MCAR)
 # 2. Fit model on only variables with complete data. (Bad idea)
 # 3. Impute (mean)
 
 # option 1 - raw proportions
 if(method == "prop"){
  
  gr_weights <- cbind(datgr, sqwgt = sqwgt) %>% 
   group_by(a) %>% 
   filter(!is.na(a)) %>% 
   summarise(sqwgt = sum(sqwgt))
  
  # this should preserve the proportions for each category from the original dataset
  gr_props <- gr_weights$sqwgt / sum(gr_weights$sqwgt)
  pp <- matrix(rep(gr_props, nmiss), nrow = nmiss, byrow = TRUE)
 }
 
 # option 2 - fully observed variables
 if(method == "full_obs"){
  mform <- formula(paste("a ~ ", paste(num_nonmiss,
                                       collapse = "+")))
  invisible(capture.output(mfit <- nnet::multinom(mform, datgr, na.action=na.exclude, weights = sqwgt)))
  pp <- predict(mfit, newdata = datgr[unlist(id_miss),], type = "probs")
 }
 
 # option 3 - mean imputation 
 if(method == "mean_imp"){
  tmp <- datgr
  num_cols <- names(tmp)[sapply(tmp, is.numeric)]
  for(col in num_cols){
   tmp[is.na(tmp[,col]),col] <- weighted.mean(unlist(tmp[,col]), w = sqwgt, na.rm = TRUE)
  }
  
  mform <- formula(paste("a ~ ", paste(setdiff(names(tmp)[numvars],"miss_pat"), 
                                       collapse = "+")))
  invisible(capture.output(mfit <- nnet::multinom(mform, tmp, na.action=na.exclude, weights = sqwgt)))
  pp <- predict(mfit, newdata = tmp[unlist(id_miss),], type = "probs")
 }
 
 # add observations to original data frame and regroup
 # if prior squashing weights are present, multiply by group probability
 datgr[,"(weight)"] <- sqwgt # this will be 1 if
 dat_ext <- datgr[-unlist(id_miss),] %>% ungroup
 
 for(j in 1:ncol(pp)){
  tmp <- datgr[unlist(id_miss),]
  tmp$a <- levels(tmp$a)[j] # assign value "a"
  tmp[,'(weight)'] <- pp[,j] * tmp[,'(weight)'] # assign probability of being in group (times existing weight)
  dat_ext <- rbind(dat_ext, tmp)
 }
 
 # regroup
 datgr <- dat_ext %>% group_by_if(~!is.numeric(.))  
 
 return(datgr)
}


## squash is a generic function
squash_miss <- function(obj, ...)
 UseMethod('squash_miss', obj)


## squash numeric data matrix (i.e., for an individual partition)
## dat   - numeric matrix
## alpha - degree of squashing (see 'reduced_sample_size') 
## ...   - arguments passed to 'optim'
squash_miss.matrix <- function(dat, 
                               alpha=1, 
                               order = 2,
                               Estep = FALSE,
                               method='CG', 
                               control=list(maxit=5000), 
                               min_obs = 3,
                               ...) {
 
 ## stop if not all data are numeric
 if(!is.numeric(dat))
  stop("'dat' must be a numeric matrix")
 
 ## add weight to original data
 if("(weight)" %nin% colnames(dat))
  dat %<>% cbind("(weight)" = 1)
 
 ## return dataframe as is if too few observations exist
 if(nrow(dat) < min_obs) return(dat)
 
 ## full data sample size/dimension
 ## calculate squashed sample size based on weights rather than sample size
 # n <- nrow(dat)
 n <- sum(dat[,"(weight)"])
 p <- ncol(dat)-1 # -1 for weight
 
 ## if too few observations are in group, return full group
 if(n < min_obs) return(dat)
 ## calculate moments for full data with missing values
 if(Estep){
  mmt <- compute_moments_miss(dat)
 } else{
  mmt <- compute_moments(dat, order)
 }
 
 ## temporarily fill in values with column means before creating pseudo data
 dat_m <- zoo::na.aggregate(dat)
 
 ## reduced sample size
 m <- reduced_sample_size(n, alpha)
 
 ## created inital pseudo data for first partition
 dat_m <- dat_m[sample(n, m),]
 
 ## store some info about the squashed data
 dmn_m <- dimnames(dat_m)
 
 ## weights for obj. fun; means and vars get priority
 u <- c(1000, # sample size
        rep(1000, p), # means
        rep(750, p), # variances
        rep(250, p*(p+1)/2 - p)) # covariances
 
 if(order >= 3) u <- c(u, rep(250, p*(p+1)*(p+2)/6))
 if(order == 4) u <- c(u, rep(50, p*(p+1)*(p+2)*(p+3)/24))
 
 ## compute ranges (extended) for each variable
 extendrange <- function(x, f=0.05) {
  r <- range(x, na.rm=TRUE)
  r + c(-f, f) * (diff(r) + f)
 }
 
 rng <- apply(dat[,-ncol(dat)], 2, extendrange) %>%
  cbind('(weight)'=c(0,n))
 
 ## vectors of min and max values
 ymn <- rep(rng[1,], rep(m,p+1)) %>% matrix(m)
 ymx <- rep(rng[2,], rep(m,p+1)) %>% matrix(m)
 
 ## least-squares search function
 f <- function(y){
  ## reconstruct data
  dat_m <- matrix(logi(y, ymn, ymx), nrow=m)
  
  ## compute moments for reduced data
  ## there aren't any missing values
  ## so compute_moments can be used
  mmt_m <- compute_moments(dat_m, order)
  
  ## weighted sum of squares for moments
  sum(u * (mmt - mmt_m)^2)  
 }
 
 opt <- optim(ilogi(dat_m, ymn, ymx), f, method=method, control=control, ...)
 
 if(opt$convergence)
  # stop("failed convergence ", opt$message)
  warning("failed convergence ", opt$message)
 
 ## reconstruct reduced data
 dat_m <- logi(opt$par, ymn, ymx)
 
 return(dat_m)
}


# Modified version to allow for missingness in categorical variables
squash_miss.data.frame <- function(dat, alpha=1,
                                   order = 2,
                                   method='CG', 
                                   Estep = c("All","Continuous","Categorical","None"),
                                   cluster_numeric = TRUE,
                                   cluster_method = c("spheres", "hierarchical"),
                                   Ecat_method = c("mean_imp","prop","full_obs"),
                                   depth = 1.5,
                                   control=list(maxit=50000)) {
 
 # load libraries here so that parallelization will be easier
 library('dplyr')
 library('magrittr')
 library('gdata')
 library('PerformanceAnalytics')
 
 Estep <- match.arg(Estep)
 if(!(Estep %in% c("All","Continuous","Categorical","None"))) 
  stop("Missingness must be one of the following options: All,Continuous,Categorical,None")
 
 cluster_method <- match.arg(cluster_method)
 Ecat_method <- match.arg(Ecat_method)
 
 # separate weights if present
 if("(weight)" %in% names(dat)){
  sqwgt <- dat$`(weight)`
  dat <- dat[,-which(names(dat) == "(weight)")]
 } else{
  sqwgt <- rep(1, nrow(dat))
 }
 
 # numeric and NA variables
 numvars <- sapply(dat, is.numeric)
 navars <- sapply(dat, function(x) any(is.na(x)))
 nacat <- !numvars & navars
 num_nonmiss <- names(dat)[numvars & !navars]
 
 # cluster based on numeric variables
 if(cluster_numeric){
  
  # if data spheres option is selected
  if(cluster_method == "spheres"){
   # calculate data spheres based on partition of observed data
   dat <- data_sphere_partition_miss(dat) 
  }
  
  if(cluster_method == "hierarchical"){
   dst <- cluster::daisy(dat[,numvars], metric = "euclidean", stand = TRUE, weights = sqwgt)
   hc <- fastcluster::hclust(dst)
   dat$clu <- as.factor(cutree(hc, h=max(hc$height)/depth))
  }
  
 }
 
 # create missingness patterns in numeric variables
 if(Estep %in% c("Categorical","None") & any(navars)){
  dat$miss_pat <- missing_pattern(dat[,names(numvars)[numvars]])
 }
 
 # group by categories and clusters if specified
 datgr <- dat %>% group_by_if(~!is.numeric(.)) 
 
 # check minimum cluster size
 mincl <- min(sapply(attr(datgr, "groups")$.rows, length))
 if(mincl < 10) warning(paste("Minimum numeric cluster size is very small:", mincl))
 
 # if missingness in any categorical variables
 if(Estep %in% c("All","Categorical")){
  datgr <- Estep_cat(datgr, method = Ecat_method, sqwgt = sqwgt)
 } else{
  datgr[,'(weight)'] <- 1
 }
 
 if(sum(datgr$`(weight)`) != sum(sqwgt)) stop("Sum of weights is not equal to sample size")
 
 ## squash numeric data by group
 dat_m <- group_modify(datgr, function(x, y) {
  
  ## remove columns with all missing before squashing
  mis <- x %>% select_if(~all(is.na(.))) %>% distinct()
  obs <- x %>% select_if(~!all(is.na(.)))
  
  # evaluate expectation of numeric variables
  Estep_cont <- Estep %in% c("All","Continuous")
  
  ## squash numeric data
  squ <- as.data.frame(squash_miss(as.matrix(obs),
                                   alpha, 
                                   order,
                                   Estep_cont,
                                   method, 
                                   control))
  
  ## reconstruct data
  merge(squ, mis) %>%
   select(names(x), '(weight)')
 })
 
 dat_m %<>%
  ungroup %>%
  select(setdiff(names(dat), c("clu","miss_pat","(partition)")), '(weight)')
 
 return(dat_m)
}



## --------------------------------------------------------
## Simulation functions -----------------------------------
## --------------------------------------------------------

## simulate dataset with ncont numeric variables and ncat
## categories in one categorical variable, with varying prevalences.
sim_dat_cat <- function(n = 5e4, 
                        rho = 0.4,
                        ncont = 5,
                        ncat = 6)
{
 
 # means of numeric and categorical variables
 mu_num = rep(0, ncont)
 mu_cat = seq(2,-2,length.out = ncat)
 
 # generate continuous random variables
 q <- length(mu_num)
 nbin <- length(mu_cat)
 sig <- matrix(rho, q + nbin, q + nbin)
 diag(sig) <- 1
 x <- MASS::mvrnorm(n,c(mu_num,mu_cat),sig)
 xcont <- x[,1:q]
 colnames(xcont) <- paste0("x",1:ncol(xcont))
 
 # create binary variables
 xmult <- x[,-c(1:q)]
 # predicted probabilities
 pp <- exp(xmult) / (1+exp(xmult))
 
 # generate multinomial variable - pp don't need to be scaled
 xmult <- factor(apply(pp, 1, function(p) which(rmultinom(1,1,p)>0)))
 
 return(data.frame(xcont, a = xmult))
}

## generate a response variable
gen_response <- function(dat, 
                         form = as.formula(~ x1 + I(x1^2) + x2 + x3 + a), 
                         beta =  c(5,2,-0.5,-2,0, # continuous
                                   -2,0,0,0,2), # categorical
                         sigma = 2){
 mm <- model.matrix(form, dat)
 if(ncol(mm) != length(beta)) stop("Formula dimension does not match length of parameter vector")
 yhat <- mm %*% beta
 err <- rnorm(nrow(mm), 0, sigma)
 return(yhat+err)
}



## Assign missing values to a dataset. Missingness patterns and weights can be 
## specified through "pat" and "wgts". If unspecified, missingness will be 
## assigned to one categorical variable and two numeric variables
amp_dat <- function(dat, type = c("MAR","MCAR","MNAR"),
                    prop = 0.5, pat = NULL, wgts = NULL){
 
 cat <-  sapply(dat, is.factor)
 ncont <- sum(!cat)-1
 ncat <- sum(cat)
 
 if(ncat < 1) stop("There must be at least one categorical variable")
 if(ncont < 1) stop("There must be at least two continuous variables")
 
 type <- match.arg(type)
 nms <- c("mcar","mar","weak mar","weak mar","mnar","weak mnar")
 
 if(is.null(pat)){
  pat <- matrix(c(1, 0, rep(1,ncont+ncat-1),  # missing first numeric variable only
                  1,1,0,rep(1,ncont+ncat-2),  # missing second numeric variable only
                  0,1,1,rep(1,ncont+ncat-2),   # missing outcome only
                  1,rep(1,ncont),0,rep(1,ncat-1), # missing categorical variable only
                  1,0,0,rep(1,ncont+ncat-2), # missing first and second numeric variables
                  1,0,0,rep(1,ncont-2),0,rep(1,ncat-1)), # missing both numeric and one categorical
                nrow = 6, byrow = TRUE)
  type <- "MAR"
 }
 
 if(is.null(wgts)){
  amp <- suppressWarnings(mice::ampute(dat, prop = prop, patterns = pat, mech = type))
 } else{
  amp <- suppressWarnings(mice::ampute(dat, prop = prop, patterns = pat, weights = wgts))
 }
 
 amp$amp$a <- factor(amp$amp$a)
 return(amp$amp)
}


## estimate model with fiml. If weights are present in the dataset
## with the name "(weight)", they will be used in the fitting process.
## Standard errors are based on the inverse observed information matrix.
est_fiml <- function(form, dat, outcome_var = "y"){
 
 if(is.character(form)) form <- as.formula(form)
 
 options(na.action='na.pass')
 mm <- model.matrix(form, dat)[,-1]
 colnames(mm) <- gsub("I\\(|\\)","",colnames(mm))
 colnames(mm) <- gsub("\\^2","sq",colnames(mm))
 
 dat_sem <- data.frame(y = dat[,outcome_var], mm)
 names(dat_sem) <- c(outcome_var,colnames(mm))
 
 reg_form <- paste(outcome_var, " ~ ", paste(colnames(mm), 
                                             collapse = " + "))
 
 if("(weight)" %in% names(dat)){
  dat_sem$wgt <- dat$`(weight)`
  
  fiml_fit <- suppressWarnings(lavaan::sem(reg_form,
                                           data = dat_sem,
                                           missing="fiml",
                                           fixed.x = FALSE, # necessary for FIML
                                           sampling.weights = "wgt",
                                           meanstructure = TRUE)) # estimate intercept and residual error sd
  
  # # when weights aren't present, it uses observed FIM
  vcov_oFIM <- solve(lavaan::lavInspect(fiml_fit, "information.observed")) / sum(dat_sem$wgt)
  fiml_fit@ParTable$se <- sqrt(diag(vcov_oFIM))
  
  
 } else{
  fiml_fit <- lavaan::sem(reg_form,
                          data = dat_sem,
                          missing="fiml",
                          fixed.x = FALSE)
 }
 
 p <- lavaan::parameterEstimates(fiml_fit)
 p <- p[p$lhs == outcome_var,]
 
 rearrange <- function(x) c(x[length(x)], x[-length(x)])
 
 out <- cbind(rearrange(p$est), rearrange(p$se))
 rownames(out) <- c("(Intercept)", rearrange(p$rhs)[-1])
 colnames(out) <- c("est","se")
 out
}


## plot ecdf for continuous variables in squashed sample and full dataset
plot_sq_ecdf <- function(dat, datsq, datmsq = NULL){
 
 num_vars <- grep("x", names(dat), value = "TRUE")
 
 ecdf_est <- lapply(num_vars, function(x){
  Hmisc::wtd.Ecdf(unlist(datsq[,x]), weights = datsq$`(weight)`)
 })
 
 if(!is.null(datmsq)){
  ecdfm_est <- lapply(num_vars, function(x){
   Hmisc::wtd.Ecdf(unlist(datmsq[,x]), weights = datmsq$`(weight)`)
  })
 }
 
 par(mfrow = c(length(num_vars),1))
 for(i in 1:length(num_vars)){
  plot(ecdf(dat[,num_vars[i]]), main = "", xlab = num_vars[i])
  points(ecdf_est[[i]]$x, ecdf_est[[i]]$ecdf)
  if(!is.null(datmsq)) points(ecdfm_est[[i]]$x, ecdfm_est[[i]]$ecdf, col = "red")
 }
 
 par(mfrow = c(1,1))
}


## plot categorical variable proprtions in squashed sample and full dataset
plot_sq_prop <- function(dat, datsq, datmsq){
 library(gridExtra)
 library(ggplot2)
 cat_vars <- grep("a", names(dat), value = "TRUE")
 
 plist <- vector("list", length(cat_vars))
 for(i in 1:length(cat_vars)){
  
  # proportions in original dataset
  p0 <- prop.table(table(dat[,cat_vars[i]]))
  
  # weighted proportions in squashed dataset
  psq <- weights::wpct(unlist(datsq[,cat_vars[i]]), weight = datsq$`(weight)`)
  psqm <- weights::wpct(unlist(datmsq[,cat_vars[i]]), weight = datmsq$`(weight)`)
  
  tmp <- data.frame(value = c(p0,psq,psqm), 
                    category = rep(names(p0),3), 
                    method = c(rep("Full",length(p0)),
                               rep("Squashed",length(psq)),
                               rep("Squashed (miss)",length(psqm))))
  
  plist[[i]] <- ggplot(tmp, aes(fill=category, y=value, x=method)) + 
   geom_bar(position="fill", stat="identity")
 }
 
 if(length(plist)>1)
  do.call("grid.arrange", c(plist, ncol=length(cat_vars)))
 else
  plist[[1]]
}



