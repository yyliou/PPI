library("lubridate")
library("zoo")
library("magrittr")
library("dplyr")
library("hpiR")
library("Metrics")
library("glmnet")
library("sp")
library("data.table")
library("spdep")
library("spData")
library("tidyverse")  
library("spatialreg")
library("rgdal")
library("rgeos")

#install.packages('spDataLarge',
#                 repos='https://nowosad.github.io/drat/',
#                 type='source')

library("spDataLarge")

# function begin
ppi <- function(price,date,areas,object,
                invar = NULL,
                neighbor = 3,
                spvar = c('longitude','latitude'),
                method = "ols",
                mavar = NULL,
                ci = .9,
                family = "binomial"){
  result <- list()
  data <- object
  names(data)[names(data) == price] <- "p"
  names(data)[names(data) == date ] <- "date"
  names(data)[names(data) == areas] <- "a"
  data$year <- year(data$date)
  data$month <- month(data$date)
  data$ym <- as.factor(as.yearmon(paste(data$year,data$month,sep = "-")))
  data$N <- as.numeric(data$ym)
  data$lnap <- log(data$p/data$a)
  data$actual <- data$lnap
  data <- data[order(data$N),]
  # modifiy data
  data <- data[complete.cases(data$date),]
  data <- data[complete.cases(data[,spvar]),]
  data <- data[complete.cases(data$N),]
  data <- data[!duplicated(data[,spvar]),] # do not allow duplicated data
  x <- data.matrix(data[, invar])
 
  #lasso deduction
  y <- data$lnap
  cv_model <- cv.glmnet(x, y, alpha = 1)
  best_lambda <- cv_model$lambda.min
  best_model <- glmnet(x, y, alpha = 1, lambda = best_lambda)
  result[[2]] <- coef(best_model)
  data$lasso_pred <- predict(best_model, s = best_lambda, newx = x)
  data$lnap <- data$lnap - data$lasso_pred
  # h-correction & ipw
  if(method == "heck"|method == "ipw"){
    fm <- as.formula(paste0("binary ~", mavar))
    mill <- list()
    for( i in min(data$N)+1:max(data$N)){
      hco <- data[data$N == min(data$N)|data$N == i,]
      hco$binary <- ifelse(hco$N > min(hco$N),1,0)
      hco_model <- glm(fm,data = hco,family = "binomial")
      hco$mill <- predict(hco_model, newdata = hco, type = "response")
      mill[[i-1]] <- hco
    }
    mill <- as.data.frame(rbindlist(mill,idcol=T))
    mill$.id <- NULL
    first <- mill[mill$N == min(mill$N),]
    a <- first %>%
      group_by(first[,1:length(first)-1]) %>%
      summarise(mill = mean(mill))
    mill <- mill[mill$N > min(mill$N),]
    data <- rbind(a,mill)
    data$ym <- as.factor(as.yearmon(paste(data$year,data$month,sep = "-")))
    if(method == "heck"){
      m <- lm(lnap ~ ym + mill,data = data)
    }
    if(method == "ipw"){
      data$weight <- ifelse(data$N != min(data$N),
                            1/data$mill,1/(1-data$mill))
      m <- lm(lnap ~ ym,data = data, weight = weight)
    }
  }
  # without solving endogenity
  if(method == "ols"){
    m <- lm(lnap ~ ym,data = data)
  }
  data$pred <- predict(m, newdata = data, type = "response")
  # spatial deduction
  sp_list <- list()
  rho_file <- data[!duplicated(data$ym), ]
  rho_file <- as.data.frame(rho_file[,'ym'])
  rho_file$rho <- NA
  names(rho_file)[1] <- "ym"
  for( i in min(data$N):max(data$N)){
    sp <- data[data$N == i,]
    nc <- data.matrix(sp[, spvar])
    nc <- knearneigh(nc, k=neighbor, longlat = T)
    nb <- knn2nb(nc)
    listw <- nb2listw(nb) 
    reg <- lagsarlm(lnap ~ 1, data = sp, listw)
    rho_file[i,2] <- summary(reg)$rho
    rho_file[i,3] <- summary(reg)$rho.se
    sp_pred <- as.data.frame(predict(reg))
    sp <- cbind(sp,sp_pred)
    sp$lnap <- sp$lnap - sp$fit
    sp$trend <- NULL
    sp$signal <- NULL
    sp_list[[i]] <- sp
  }
  rho_file$lb <- rho_file$rho - rho_file$V3*qnorm(1-(1-ci)/2)
  rho_file$ub <- rho_file$rho + rho_file$V3*qnorm(1-(1-ci)/2)
  result[[1]] <- rho_file
  data <- rbindlist(sp_list,idcol=T)
  # variation
  data$final_pred <- data$pred + data$lasso_pred + data$fit
  out <- data.frame(
    coef = summary(m)$coefficients[
      2:(max(as.numeric(data$ym))-min(as.numeric(data$ym))+1),1],
    se = summary(m)$coefficients[
      2:(max(as.numeric(data$ym))-min(as.numeric(data$ym))+1),2])
  out$index <- (exp(out$coef))*100
  out$lb <- (exp(out$coef - out$se*qnorm(1-(1-ci)/2)))*100
  out$ub <- (exp(out$coef + out$se*qnorm(1-(1-ci)/2)))*100
  result[[3]] <- out
  data$lasso_r <- (data$actual-data$lasso_pred)^2
  data$index_r <- (data$actual-data$lasso_pred-data$pred)^2
  data$sp_r <- (data$actual-data$lasso_pred-data$pred-data$fit)^2
  data$tv1 <- (data$actual - mean(data$actual))^2
  data$tv2 <- (data$actual-data$lasso_pred-mean(data$actual-data$lasso_pred))^2
  data$tv3 <- (data$actual-data$lasso_pred-data$lasso_pred - 
                 mean(data$actual-data$lasso_pred-data$lasso_pred))^2
  lasso.r2 <- 1-sum(data$lasso_r)/sum(data$tv1)
  index.r2 <- (1-lasso.r2)*(1-sum(data$index_r)/sum(data$tv2))
  spatial.r2 <- (1-lasso.r2-index.r2)*(1-sum(data$sp_r)/sum(data$tv3))
  resid.r2 <- 1-lasso.r2-index.r2-spatial.r2
  r2 <- rbind(index.r2,lasso.r2)
  r2 <- rbind(r2,spatial.r2)
  r2 <- rbind(r2,resid.r2)
  rmse <- rmse(data$actual, data$final_pred)
  result[[4]] <- rbind(r2,rmse)
  result
}
# example
# data(seattle_sales)
# seattle_sales
# data(ex_sales)
# ex_sales

res <- ppi(price  = "sale_price",
           date   = "sale_date",
           areas  = "lot_sf",
           object = ex_sales,
           method = "ipw",
           invar  = c('age','area','baths','beds','bldg_grade','eff_age',
                      'latitude','longitude','use_type','wfnt'),
           neighbor = 3,
           spvar = c('longitude','latitude'),
           mavar  = "age + baths + beds")

# spatial correlation
res[[1]]

# coef
res[[2]]

# index
res[[3]]

# variation
res[[4]]
