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
library("fastDummies")

#install.packages('spDataLarge',
#                 repos='https://nowosad.github.io/drat/',
#                 type='source')

library("spDataLarge")
data <- ex_sales
# function begin
ppi <- function(price,date,areas,object,invar,catvar,
                neighbor = 3,
                spvar = c('longitude','latitude'),
                method = "ols",
                mavar = NULL,
                ci = .9,
                train = .9,
                family = "binomial"){
  # basic
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
  # category var
  cat <- data[, catvar]
  data <- data[,!(names(data) %in% catvar)]
  cat <- dummy_cols(cat, select_columns = catvar)
  cat <- cat[,!(names(cat) %in% catvar)]
  catname <- names(cat)
  data <- cbind(data,cat)
  # modify data
  data <- data[,]
  data <- data[complete.cases(data[,spvar]),]
  data <- data[complete.cases(data$N),]
  data <- data[!duplicated(data[,spvar]),] # do not allow duplicated data
  x <- data
  y <- data[,c("lnap","N")]
  tind <- round(max(x$N)*train)
  x_train   <- x[x$N <  tind,]
  x_test    <- x[x$N >= tind,]
  y_train   <- y[y$N <  tind,]
  y_test    <- y[y$N >= tind,]
  x_train   <- data.matrix(x_train[, c(invar,catname)])
  x_test    <- data.matrix(x_test[, c(invar,catname)])
  y_train$N <- NULL
  y_test$N  <- NULL
  y_train   <- as.matrix(y_train)
  y_test    <- as.matrix(y_test)
  #lasso
  cv_model <- cv.glmnet(x_train, y_train, alpha = 1)
  best_lambda <- cv_model$lambda.min
  best_model <- glmnet(x_train, y_train, alpha = 1, lambda = best_lambda)
  ridge <- glmnet(x_train, y_train, alpha = 0, lambda = best_lambda)
  linear_use <- as.data.frame(cbind(y_train,x_train))
  linear <- lm(lnap ~ .,data = linear_use)
  result[[2]] <- data.frame(
    Linear  = linear$coefficients,
    Lasso   = as.vector(coef(best_model)),
    Ridge   = as.vector(coef(ridge))
  )
  # Compute R^2 from true and predicted values
  eval_results <- function(true, predicted, df) {
    SSE <- sum((predicted - true)^2)
    SST <- sum((true - mean(true))^2)
    R_square <- 1 - SSE / SST
    RMSE = sqrt(SSE/nrow(df))
    # Model performance metrics
    data.frame(
      RMSE = RMSE,
      Rsquare = R_square
    )
  }
  pred_lasso <- predict(best_model, s = best_lambda, newx = x_test)
  pred_ridge <- predict(ridge, s = best_lambda, newx = x_test)
  pred_linear <- predict(linear, newdata = as.data.frame(x_test))
  lasso <- eval_results(y_test, pred_lasso, x_test)
  ridge <- eval_results(y_test, pred_ridge, x_test)
  linear <- eval_results(y_test, pred_linear, x_test)
  per <- rbind(lasso,ridge)
  per <- rbind(per,linear)
  rownames(per) <- c("lasso","ridge","linear")
  result[[3]] <- per
  x <- rbind(x_train,x_test)
  data$lasso_pred <- predict(best_model, s = best_lambda, newx = x)
  data$lnap <- data$lnap - data$lasso_pred
  # heckman & ipw
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
  # ols
  if(method == "ols"){
    m <- lm(lnap ~ ym,data = data)
  }
  data$pred <- predict(m, newdata = data, type = "response")
  # spatial
  sp_list <- list()
  rho_file <- data[!duplicated(data$ym), ]
  rho_file <- as.data.frame(rho_file[,'ym'])
  rho_file$rho <- NA
  names(rho_file)[1] <- "ym"
  geo <- list()
  for( i in min(data$N):max(data$N)){
    sp <- data[data$N == i,]
    nc.cord <- data.matrix(sp[, spvar])
    nc <- knearneigh(nc.cord, k=neighbor, longlat = T)
    nb <- knn2nb(nc)
    plot(nb,nc.cord)
    geo[[i]] <- recordPlot()
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
  result[[8]] <- geo
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
  result[[4]] <- out
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
  result[[5]] <- rbind(r2,rmse)
  # Index Plotting
  col <- data.frame(as.yearmon(gsub("ym","",rownames(result[[4]]))))
  rownames(result[[4]]) <- NULL
  result[[4]] <- cbind(col,result[[4]])
  names(result[[4]])[1] <- "ym"
  a1 <- data.frame(ym = min(as.yearmon(data$ym)),
                   coef = 0,se = 0,index = 100,lb = 100,ub = 100)
  result[[4]] <- rbind(a1,result[[4]])
  dfplot <- result[[4]]
  dfplot$se <- NULL
  dfplot$coef <- NULL
  names(dfplot) <- c("ym","Index","Lower Bond","Upper Bond")
  dfplot <- dfplot %>% gather(key, value, -ym)
  result[[6]] <- ggplot(dfplot, mapping = aes(x = ym, y = value, color = key)) + 
    geom_line() + scale_color_manual(values=c("darkred", "gray","gray")) +
    labs(x = 'Month',y = 'Index',colour="Legend",
         title = 'Monthly Property Price Index (PPI)') +
    geom_hline(yintercept=100, linetype="dashed", color = "red")
  # Spatial Plotting
  dfplot <- result[[1]]
  dfplot$ym <- as.yearmon(dfplot$ym)
  dfplot$V3 <- NULL
  names(dfplot) <- c("ym","Rho","Lower Bond","Upper Bond")
  dfplot <- dfplot %>% gather(key, value, -ym)
  result[[7]] <- ggplot(dfplot, mapping = aes(x = ym, y = value, color = key)) + 
    geom_line() + scale_color_manual(values=c("gray", "darkred","gray")) +
    labs(x = 'Month',y = 'Index',colour="Legend",
         title = 'Spatial Correlation Index') +
    geom_hline(yintercept=0, linetype="dashed", color = "red")
  result
}

# example
# data(seattle_sales)
# seattle_sales
# data(ex_sales)
# ex_sales
# ls(ex_sales)

res <- ppi(price  = "sale_price",
           date   = "sale_date",
           areas  = "lot_sf",
           object = ex_sales,
           method = "ipw",
           invar  = c('age','baths','beds','bldg_grade',
                      'eff_age','tot_sf','wfnt'),
           catvar = c('area','use_type'),
           neighbor = 3,
           spvar = c('longitude','latitude'),
           mavar  = "age + baths + beds")

# spatial correlation
res[[1]]

# coef
res[[2]]

# performance
res[[3]]

# index
res[[4]]

# variation
res[[5]]

# index plot
res[[6]]

# spatial corr plot
res[[7]]

# map
res[[8]][[5]]
