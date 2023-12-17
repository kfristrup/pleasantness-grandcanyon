install.packages(c("beepr", "Cairo", "data.table", "future.apply", "gamm4",
"ggplot2", "ineq", "lme4", "MuMIn", "ordinal", "party", "progressr",
"purrr", "readxl", "robustbase", "twosamples"))
sessionInfo()
sort( sapply(ls(),function(x){object.size(get(x))}))
rm(list=ls())
library(beepr)
library(Cairo)
library(data.table)
library(future.apply)
library(gamm4)
library(ggplot2)
library(ineq)
library(lme4)
library(MuMIn)
library(ordinal)
library(party)
library(progressr)
library(purrr)
library(readxl)
library(robustbase)
library(twosamples)
# skip the IF statement to run all processing in single thread
# kfPC: must reset Rprofile.site to be simple, not Intel oneAPI
# could use parallely::supportsMulticore() when package is available
#options(future.globals.maxSize= 500*1024^2)
if ("Darwin" == Sys.info()["sysname"])
	plan(multicore) else # parallel ops using fork
		plan(multisession) #
measurableThreshold <- 20 #global test value, smallest measured were 30+ dB
### Utility functions for models
termList <- function(modList)
  return(sort(unique(
    unlist(lapply(lapply(lapply(modList, formula),terms),attr,"term.labels")))))
varList <- function(trmLst)
  return(sort(sub(patt="1 \\| ",repl="",unique(unlist(sapply(trmLst,strsplit,":"))))))
formuSort <- function(frmla){
  lhs <- sub(patt="~.+", repl="", frmla)
  trms <- termList(frmla)
  randTerms <- grep(patt="\\|", trms)
  trms[randTerms] <-
    sapply(trms[randTerms], function(tm) paste0("(",tm,")"))
  return(paste(paste0(lhs,"~ "),
               paste(trms, collapse=" + ")))
}
formulasUnique <- function(fmList){
  tmp <- sort(unique(sapply(fmList,formuSort)))
  names(tmp)<- NULL
  return(tmp)
}
makeFormulae <- function(target, vnames)
  # creates one formula for each element of vnames
  return(sapply(vnames, function(x) paste0(target, " ~ ", x, sep="")))
multiplyFormulae <- function(target, vVector, mdls)
  # creates replicates of the existing models by adding each of vVector
  return(c(sapply(vVector, function(x) sub(patt="~ ",
                                         repl=paste0("~ ",x," + "), mdls))))
factorialFormulae <- function(target, vCombos, mdls,
                              facDepth = length(vCombos)){
  # creates a factorial expansion of mdls by adding all combinations of vCombos
  # this includes zero factors in vCombos, so the original models are included
  gridFactors <- vector(mode="list", length=length(vCombos))
  gridFactors <- lapply(gridFactors, function(x) x <- c(F,T))
  fcmbn <- apply(expand.grid(gridFactors), 1, function(x) vCombos[x])
  frms <- sapply(
    sapply(sapply(fcmbn[facDepth >= sapply(fcmbn,length)],
                  sapply, function(x)
                    paste(x, "+")), paste, collapse=" "),
    function(x) paste("~", x))
  return(c(sapply(frms, function(x)
    sub(patt="~ ", repl = paste0(x," "), mdls))))
}
frmuExtract <- function(mAvSmTab, tgt){
  # extracts text formulae from a model average table
  if(is.null(nms <- names(mAvSmTab)) |
              !all(nms == c("df","logLik","AICc","delta","weight")))
    stop("need model averaged table")
  if(0==
     sum(sapply(sapply(dimnames(mAvSmTab)[[1]],
                       grep, patt="/", fixed=T),
                length))
     ){
    mdlNums <- lapply(sapply(dimnames(mAvSmTab)[[1]], strsplit, ""),
                      as.numeric)
  } else {
    mdlNums <- lapply(
      sapply(
        dimnames(mAvSmTab)[[1]],strsplit,"/"),
      as.numeric)
  }
  sapply(mdlNums, function(vrs)
    paste(tgt," ~ ",
          paste(names(attr(mAvSmTab,"term.codes"))[vrs], collapse=" + "),
          sep=""))
}
modSumOut <- function(modList, tgt){
  # list of fitted models, plus string labeling the dependent variable
  # returns a list with model summary and variable summary
  # the model summary contains coefficient summaries for the simple variables
  # the row name and first six entries in the last nonmodel row are used to
  # return summaries of the random factor Std Dev
  hessTst <- sapply(lapply(modList,summary), "[[", "condHess")
  iKeep <- !is.na(hessTst)
  modsAvg <- model.avg(modList[iKeep])
  mAvgSumm <- summary(modsAvg)
  mSumTab <- mAvgSumm$msTable
  mSumTab <- mSumTab[cumsum(mSumTab$weight) < 0.99999,] # retain 99.999%
  mSumTab <- cbind(frmuExtract(mSumTab, tgt),
                   mSumTab)
  if(0==
     sum(sapply(sapply(dimnames(mSumTab)[[1]],
                       grep, patt="/", fixed=T),
                length))
  ){
    frmNumCh <- sapply(dimnames(mSumTab)[[1]], strsplit, "")
  } else {
    frmNumCh <- sapply(dimnames(mSumTab)[[1]],strsplit,"/")
  }
  fNumList <- lapply(frmNumCh, as.numeric)
  varIncluded <- matrix(nrow = length(frmNumCh),
                        ncol = max(as.numeric(unlist(fNumList))))
  for (irw in seq(along=varIncluded[,1]))
    varIncluded[irw,fNumList[[irw]]] <- 1
  dimnames(varIncluded)[[2]] <- names(attr(mAvgSumm$msTable,"term.codes"))
  varIncluded[is.na(varIncluded)] <- 0
  clmnOrder <- order(apply(varIncluded*mSumTab$weight,2,sum),
                     decreasing = T)
  varIncluded <- varIncluded[,clmnOrder]
  termWtsum <- apply(varIncluded*mSumTab$weight,2,sum)
  coefMat <- mAvgSumm$coefmat.subset
  mSumTab <- cbind(rbind(NA, mSumTab),
                   rbind(termWtsum,varIncluded))
  names(mSumTab) <- gsub(patt="[12]+$",repl="",x=names(mSumTab))
  dimnames(coefMat)[[1]] <- gsub(patt="[12]+$",repl="",
                                 x=dimnames(coefMat)[[1]])
  if(all(sapply(sapply(modList,class),"==","clmm"))){
    mSumTab[1,1:6] <- summary(sapply((sapply(modList[iKeep], "[[", "ST")),c))
    dimnames(mSumTab)[[1]][1] <-
      sum(unlist(sapply(
        modList[order(sapply(modList, AICc))][
          1:(dim(mSumTab)[1]-1)], "[[","ST"))*
            mSumTab$weight[-1])/sum(mSumTab$weight[-1])
  } else if(all(sapply(sapply(modList,class),"==","glmerMod"))){
    mSumTab[1,1:6] <- summary(sapply(modList[iKeep], slot, name="theta"))
    dimnames(mSumTab)[[1]][1] <-
      sum(unlist(sapply(
        modList[order(sapply(modList, AICc))][
          1:(dim(mSumTab)[1]-1)], slot, name="theta"))*
            mSumTab$weight[-1])/sum(mSumTab$weight[-1])
  }
  vcHeader <- t(coefMat[match(names(mSumTab),
                              sub(patt = "TRUE", repl = "",
                                  x = dimnames(coefMat)[[1]])),])
  dimnames(vcHeader)[[2]] <- names(mSumTab)
  mSumTab <- rbind(vcHeader, mSumTab)
  return(list(ModlSumm = mSumTab, CoefSumm = coefMat, ModAvg = modsAvg))
}
### Utility functions for plotting
add_legend <- function(...) {
  opar <- par(fig=c(0, 1, 0, 1), oma=c(0, 0, 0, 0), 
    mar=c(0, 0, 0, 0), new=TRUE)
  on.exit(par(opar))
  plot(0, 0, type='n', bty='n', xaxt='n', yaxt='n')
  legend(...)
}
heliPlot <- function(anyHeli){
  NoHeli <- grall[Heli1==anyHeli,summary(Pleasant1),by=.(Heli1,noHeliErg)]
  NoHeli <- matrix(NoHeli$V1,ncol=2,dimnames=list(1:7,c("noHeliErg","HeliErg")))
  tstVal <- fisher.test(NoHeli,simulate.p.value = T)$p.value
  NoHeli <- t(NoHeli)
  NoHeli <- sweep(NoHeli,1,apply(NoHeli,1,sum),"/")
  midpts <- barplot(NoHeli, horiz = T, beside=T, xlab="", ylab="", axes=F,
                    xaxs="i", yaxs ="i", ylim = c(0.5, 21.5), axisnames=F,
                    xlim=xxlim, col=grys, density=dstys, angle=angls)
  axis(1,outer=T,at=(0:5)/10)
  return(tstVal)
}
laePlot <- function(grl, Pleas, brks = bbrks) {
    Nsegs0 <- nrow(grl[Pleasant1 == Pleas & Heli1 == 0])
    Nsegs1 <- nrow(grl[Pleasant1 == Pleas & Heli1 == 1])
    par(mar = c(0, 0, 0, 2.5))
    heli0 <- grl[Pleasant1 == Pleas & Heli1 == 0, hist(Erg3WoErr, breaks = brks,
        plot = F)]
    heli1 <- grl[Pleasant1 == Pleas & Heli1 == 1, hist(Erg3WoErr, breaks = brks,
        plot = F)]
    hstMat <- matrix(c(heli0$counts, heli1$counts), ncol = 2, dimnames = list(heli0$mids,
        c("NoHeli", "Heli")))
    hstMat <- t(sweep(hstMat, 2, apply(hstMat, 2, sum), "/"))
    # next four lines translate dB into x axis coordinates
    midPoints <- barplot(hstMat, beside = T, xlab = "", ylab = "", axes = F,
        yaxs = "i", axisnames = F, ylim = c(0, 1.2))
    arloc <- data.frame(x = bbrks[-c(1, length(bbrks))], y = apply(midPoints,
        2, mean)[-1])
    lmres <- lm(y ~ x, data = arloc)
    xfrm <- coef(lmres)
    xmns <- c(xfrm[1] + xfrm[2] * grl[Pleasant1 == Pleas & Heli1 == 0 & Erg3WoErr >
        30, mean(Erg3WoErr)], xfrm[1] + xfrm[2] * grl[Pleasant1 == Pleas & Heli1 ==
        1 & Erg3WoErr > 30, mean(Erg3WoErr)])
    arrows(x0 = xmns, y0 = rep(1.1, 2), x1 = xmns, y1 = rep(0.95, 2),
           col = c("#000000", "808080"), length = 0.04)
    text(x = par()$usr[1:2] %*% c(0.1, 0.9), y = par()$usr[3:4] %*% c(0.2, 0.8),
           lab = sprintf("N=%d", Nsegs0), cex=0.75)
    text(x = par()$usr[1:2] %*% c(0.1, 0.9), y = par()$usr[3:4] %*% c(0.3, 0.7),
           lab = sprintf("N=%d", Nsegs1), cex=0.75, col = "808080")
    axis(side = 2, at = c(0, 1), labels = c("0.0", "1.0"), las = 1,
         cex.axis = 0.8, line = -0.5)
    return(midPoints)
}
Rapoza <- function(LAE,SurvType){
  Icept=-7.195;Taud=0.017*77;PEheli=0.017*80;PEprop=0.003*12
  HR2 = 0.080;Ipeace=0.480*.87;Vprev=0.118*.13;Aonly=0.250*.89
  Wbirds=0.257*.41
  return(plogis(0.043*LAE+Icept+Taud+PEheli+PEprop+HR2+Ipeace+Vprev+Aonly+Wbirds))
}
SchoDR  <- function(LaeH,Plevel=7,Hli1=medline, ModifierEffects=MF){
  Plev <- SplitCoef[max(1,Plevel-1)]
  ix <-charmatch(c("Erg3WoErr","Heli1"),names(SchoCoef))
  y <- plogis(q = c(Plev) - SchoCoef[ix[1]]*LaeH -
                c(SchoCoef[ix[2]]*Hli1) - c(ModifierEffects))
  return(y)
}
SchoLines <- function(Helicopt){
  for (jj in seq(from=2,to=7)){ #assumes medline is median Hermit from above chunk
    lines(Lae,SchoDR(LaeH=Lae,Hli1=Helicopt,Plevel=jj))
    dB <- match(80-(jj-2)*9-3,Lae)
    text(x=Lae[dB]+2,y=
           SchoDR(LaeH=Lae[dB],
                  Hli1=ifelse(length(Helicopt)>1,Helicopt[dB],Helicopt),
                  Plevel=jj),
         labels=sprintf("k=%d",jj-1),adj=c(0,1))
  }
  lines(Lae,Rapoza(Lae),lty=3,lwd=2)
}
### Characterize the latent variable distributions for the best fitted model
# logit(P (Pleasantness ≤ j)) = θ_j − t(β) %*% x_i − u(Survey_i)
# return the median predicted values for each response category
# Two functions for reordering a list of integers 1:nMax
# A convenience function
latentPred <- function(clmmFitted){
  # fixed coefficients
  fCoef <- clmmFitted$beta
  # names of variables for those coefficients
  fCoefNames <- sub(patt=".$",repl="",names(hhmods[[ibest]]$beta))
  fCoefVals <- sub(patt=".*(.)$",repl="\\1",names(hhmods[[ibest]]$beta))
  predDat <- t(apply(hhmods[[ibest]]$call$data[, fCoefNames, with=F],
                     1,FUN="==",fCoefVals))
  dimnames(predDat)[[2]] <- names(hhmods[[ibest]]$beta)
  hist(clmmFitted$ranef[factor(clmmFitted$call$data$SurvNum,exclude=NULL)],
       main=NULL,xlab="Conditional Random Effect",ylab="Number of hikers")
  latentScores <- -(predDat %*% fCoef +
              clmmFitted$ranef[factor(clmmFitted$call$data$SurvNum,
                                      exclude=NULL)])
  tmp <- boxplot(latentScores ~ clmmFitted$call$data$Pleasant1,
          xlab="Pleasantness", ylab="Predicted latent variable",
          range=1.58, notch=T)
  return(latentScores)
}
evertIx <- function(nMax)
  ## inside-out ordering
  return(ceiling(nMax/2)+(1:nMax%/%2)*(-1)^(1:nMax))
minEndsIx <- function(nMax)
  ## place smallest indices at the ends, largest in the middle
  return(c(seq(1,nMax,2),seq((nMax%/%2)*2,2,-2)))
partitionVarImport <- function(dTab, target, vvec, wts){
  ## dtab is a data.table
  ## target is a string labeling the dependent variable
  ## vvec is a vector of strings naming the independent variables
  ## wts is a vector of numeric values, length = length(levels(target))
  # first the categorical variables
  isF <- sapply(vvec, function(x) is.factor(dTab[[x]]))
  catMeans <- vector(mode="list", length=sum(isF))
  names(catMeans) <- vvec[isF]
  for(iv in vvec[isF])
    catMeans[[iv]] <- sapply(
      split(dTab[,.(target=as.numeric(get(target)), wts=get(wts))],
            dTab[[iv]]), function(x)
              weighted.mean(x[, target], x[,wts], na.rm = T))
  rslt <- sapply(lapply(catMeans, range, na.rm=T),diff)
  rslt2 <- vector(mode="numeric", length=sum(!isF))
  names(rslt2) <- vvec[!isF]
  tsummary <- sort(summary(as.factor(dTab[[target]])))[
    minEndsIx(nlevels(as.factor(dTab[[target]])))]
  tsplit <- unlist(sapply(seq(along=tsummary), function(x)
    rep(as.numeric(names(tsummary)[x]),tsummary[x])))
  for(iv in vvec[!isF]){
    fsorted <- sort(dTab[[iv]])
    tmp <- split(fsorted, tsplit)
    dMax <- diff(range(sapply(tmp, mean, na.rm=T)))
    tmp <- split(fsorted, rev(tsplit))
    dMax <- max(dMax,
                diff(range(sapply(tmp, mean, na.rm=T))))
    tmpMeans <- sapply(split(dTab[[iv]], dTab[[target]]), mean, na.rm=T)
    rslt2[iv] <- diff(range(tmpMeans))/dMax
  }
  return(c(rslt,rslt2))
}
### Read and prepare the data
# demographic bar chart
srcdir <- "D:/Schomer/PranavData/"
dmog <- read_excel(paste0(srcdir, "Anderson vs GRCA Demographics.xlsx"))
dmog2 <- unlist(dmog[,2:6])
dmog3 <- data.frame(
  Pct = 100*dmog2,
  Study = as.factor(
    sub(patt="[[:digit:]]", repl="",sub(patt=" Percentages",
                                        rep="",names(dmog2)))),
  Demog = as.factor(unlist(
    dmog[as.numeric(gsub(patt="[^[:digit:]]",rep="",names(dmog2))),1]
)))
sz <- 18; CairoSVG(file = paste0(srcdir,"Output/DemogBarPlot.svg"),
         width = sz, height = sz, onefile = TRUE, bg = "white",
         pointsize = 16)
par(mar=c(4,6,4,2)+0.1, mgp=c(4,2,0))
barplot(Pct ~ Demog + Study, data=dmog3, beside=T, ylim=c(0,100),
        col=gray((0:2)/3), xlab="", ylab="Percentages",
        cex.lab=1.5, cex.axis=1.5, cex.names=1.5,
        names.arg=c("Anderson\net al. 2011", "All\nTrails", "Bright\nAngel",
                    "Hermit\nTrail", "Widforss\nTrail"))
legend(x="top", leg=levels(dmog3$Demog), fill=gray((0:2)/3),cex=1.5)
dev.off()
#
grcaqt <- fread(input=paste0(srcdir,"Number of OPs by Segment.txt"))
grcaqt$Date <- as.POSIXct(strptime(paste(as.Date(grcaqt$Date,origin="1899-12-30"),grcaqt$"Time-1"),
                                   format="%F %I:%M:%S %p"))
ix <- c("Time(24)","Seg Present","Time-1","Start Time","Seperated start times")
grcaqt <- grcaqt[,-match(ix,names(grcaqt)),with=F]
names(grcaqt) <- gsub(pattern="[\\. -/]",replacement="",names(grcaqt))
#pcol <- colorRampPalette(c("darkviolet","hotpink"))(7)
pcol <- rev(gray(seq(0,6)/7))
#plot(jitter(grcaqt$Totalseg),jitter(grcaqt$ECseg),type='p',
#  pch=".",col=pcol[grcaqt$Pleasant1],cex=3)
#legend(x="bottomright",fill=pcol,legend=1:7)

hermit <- fread(input=paste(srcdir,"GrcaHermitTabDelimited2.txt",sep=""),sep="\t")
bright <- fread(input=paste(srcdir,"Bright Angel Stacked For Use tab delimited2.txt",sep=""))
widfor <- fread(input=paste(srcdir,"Widforss Stacked tab delimited2.txt",sep=""))
bright <- bright[,apply(!is.na(bright),2,any),with=F]
names(hermit) <- gsub(pattern="[-_#\\(\\)\\. /]",replacement="",names(hermit))
names(bright) <- gsub(pattern="[-_#\\(\\)\\. /]",replacement="",names(bright))
names(widfor) <- gsub(pattern="[-_#\\(\\)\\. /]",replacement="",names(widfor))
ix <- grep(patt="^V[0-9][0-9]",names(hermit))
hermit <- hermit[,-ix,with=F]
ix <- grep(patt="^V[0-9][0-9]",names(widfor))
widfor <- widfor[,-ix,with=F]
names(hermit) <- sub(pattern="16yr",repl="X16yr",x=names(hermit))
grall <- hermit[,1:61,with=F]
bright <- bright[,1:61,with=F]
widfor <- widfor[,1:61,with=F]                                                               
names(bright) <- names(grall)
names(widfor) <- names(grall)
grall$SurvNum <- paste("h",grall$SurvNum,sep="")
bright$SurvNum <- paste("b",bright$SurvNum,sep="")
widfor$SurvNum <- paste("w",widfor$SurvNum,sep="")
grall <- rbind(grall,bright,widfor)
grall$Date <- as.POSIXct(strptime(paste(grall$Date,"-2013 ",grall$"Time1",sep=""),
                                   format="%d-%b-%Y %H:%M"))
grall[Jet1 < 0,Jet1:= 0]
grall[PleasantEOH < 0,PleasantEOH := NA]
grall[NatSoundEOH < 0,NatSoundEOH := NA]
grall[Gender == 3, Gender := NA]
grall[X16yr < 0, X16yr := NA]
grall[Age == -1,Age := NA]
grall[Age == "40/60",Age := 40]
grall[Age == "16/60",Age := 60]
grall[Age == "16/40",Age := 40]
grall[Age == "15",Age := 16]
grall[Age == "26", Age := 25]
grall[, Age:=as.factor(Age)]
nms <- c("Wind1","Jet1","Water1","Thunder1","Bird1","Prop1","Insect1",
  "Voice1","Vehicle1","Heli1","Yelling1","Walking1")
for (j in match(nms,names(grall)))
  set(grall,which(is.na(grall[[j]])),j,0)
nms <- c(nms,"Gender","FirsTime","X16yr","SurvNum")
for (j in match(nms,names(grall)))
  set(grall,which(grall[[j]] < 0),j,NA)
for (j in match(nms,names(grall)))
  set(grall,i=NULL,j=j,value=factor(grall[[j]]))
set(grall,which(grall$NQ < 0),"NQ",NA)
nms <- c("Pleasant1","PleasantEOH","NatSoundEOH","NQ")
for (j in match(nms,names(grall)))
  set(grall,i=NULL,j=j,value=ordered(grall[[j]]))
jj <- match("Age",names(grall))
set(x=grall,i=NULL,j=jj,value=as.numeric(grall[[jj]]))
grall[, ErgAvg := TotErgWoErr/SegDur]
grall[, ErgAvg1 := ErgA1WoErr/SegDur]
grall[, ErgAvg2 := ErgA2WoErr/SegDur]
grall[, ErgAvg3 :=Erg3WoErr/SegDur]
# create aircraft noise fractions
grall[, HeliFrac := ifelse(TotErgWoErr, Erg3WoErr/TotErgWoErr, 0)]
grall[, JetFrac := ifelse(TotErgWoErr, ErgA1WoErr/TotErgWoErr, 0)]
# convert all NAN to NA
for (j in seq(along=grall))
  set(grall,which(is.nan(grall[[j]])),j,NA)
# convert all P^2 energy to decibels, with 0 dB for zero energy
nms <- c("TotErgWoErr","ErgA1WoErr","ErgA2WoErr","Erg3WoErr",
         "ErgAvg","ErgAvg1","ErgAvg2","ErgAvg3","SegDur")
# zero measured energy gets converted to 1e-99 or -990 dB
for (jj in match(nms,names(grall)))
  set(grall,i=NULL,j=jj,value=10*log10(sapply(grall[[jj]],max,1e-99)))
# all trails, including trail name as a factor
setkey(grall, SurvNum, Segment)
grall[,Trail:=as.factor(substring(grall$SurvNum,1,1))]

grall[,cHeli:=cumsum(as.numeric(Heli1)-1),by=SurvNum] #as.numeric returns 1|2
grall[Heli1==1, cHeli:=cHeli-1] #remove SELF so cHeli is number previously noted
grall[, preHeli := cHeli>0]
grall[, cumSELT := 10*log10(cumsum(10^(TotErgWoErr/10))), by=SurvNum]
grall[, cumSEL1 := 10*log10(cumsum(10^(ErgA1WoErr/10))), by=SurvNum]
grall[, cumSEL2 := 10*log10(cumsum(10^(ErgA2WoErr/10))), by=SurvNum]
grall[, cumSEL3 := 10*log10(cumsum(10^(Erg3WoErr/10))), by=SurvNum]
# need to remove 
grall[, cumLaeqT := cumSELT - 10*log10(cumsum(SegDur)), by=SurvNum]
grall[, cumLaeq1 := cumSEL1 - 10*log10(cumsum(SegDur)), by=SurvNum]
grall[, cumLaeq2 := cumSEL2 - 10*log10(cumsum(SegDur)), by=SurvNum]
grall[, cumLaeq3 := cumSEL3 - 10*log10(cumsum(SegDur)), by=SurvNum]
grall[,NoErg:=Erg3WoErr==0]
grall[, HeliFirst:=Heli1[which.min(Segment)],by=SurvNum]
grall[,cJet:=cumsum(as.numeric(Jet1)-1),by=SurvNum] #as.numeric returns 1|2
grall[Jet1==1, cJet:=cJet-1] #remove SELF so cJet is number previously noted
grall[, preJet := cJet>0]
grall[, JetFirst:=Jet1[which.min(Segment)],by=SurvNum]
grall[,cProp:=cumsum(as.numeric(Prop1)-1),by=SurvNum] #as.numeric returns 1|2
grall[Prop1==1, cProp:=cProp-1] #remove SELF so cProp is number previously noted
grall[, preProp := cProp>0]
grall[, PropFirst:=Prop1[which.min(Segment)],by=SurvNum]
grall[,TotAir1 := (Heli1==1) + (Jet1==1) + (Prop1==1)]
grall[, TotAirFirst := TotAir1[which.min(Segment)], by=SurvNum]
grall[,cAirc := cumsum(TotAir1),by = SurvNum]
grall[TotAir1 > 0, cAirc := cAirc - TotAir1] #remove SELF so cAirc is number previously noted
grall[, preAirc := cAirc > 0]
grall[, cEvents := cumsum(Events), by = SurvNum]
grall[Events>0, cEvents := cEvents - Events]
grall[, preEvents := cEvents > 0]
grall[, cNp1 := cumsum(Np1), by = SurvNum]
grall[Np1 > 0, cNp1 := cNp1 - Np1]
grall[, preNp1 := cNp1 > 0]
grall[, cNp2 := cumsum(Np2), by = SurvNum]
grall[Np2 > 0, cNp2 := cNp2 - Np2]
grall[, preNp2 := cNp2 > 0]
grall[, cNp3 := cumsum(Np3), by = SurvNum]
grall[Np3 > 0, cNp3 := cNp3 - Np3]
grall[, preNp3 := cNp3 > 0]
grall[,noHeliErg := Erg3WoErr < measurableThreshold] # T if no helicopter noise
grall[,noTotErg := TotErgWoErr < measurableThreshold] # T if no aircraft noise
##### fraction of hikers spontaneously mentioning helicopters in comments

grall[grep(patt="Heli",x=grall$CommentsEOH),summary(Trail)]/
  grall[,length(unique(SurvNum)),by=Trail]$V1
grall[grep(patt="noise",x=grall$CommentsEOH),summary(Trail)]/
  grall[,length(unique(SurvNum)),by=Trail]$V1
# summary of hike duration
CairoPNG(filename=paste0(srcdir, "Output/HikeLengthComparison.png"))
plot(grall[,
           .(x=max(Date)-min(Date), y=sum(SegDur, na.rm=T)*60),
           by=SurvNum][,-1,with=T], xlab="Time range from Date (s)",
     ylab="Sum of SegDur (s)")
dev.off()
summary(grall[,unique(PleasantEOH),by=SurvNum]$V1,max=100)
DTsecs <- grall[, .(Trl=unique(Trail), dtS=as.numeric(max(Date)-min(Date))),
                    keyby=SurvNum]
SDsecs <- grall[, .(sdS=sum(SegDur, na.rm=T)*60), keyby=SurvNum]
MaxSecs <-DTsecs[SDsecs]
MaxSecs[,Msecs:=ifelse(dtS>sdS,dtS,sdS)]
hikSegs <- t(sapply(levels(grall$Trail),function(x)
  summary(as.factor(grall[Trail==x,.N,by=SurvNum]$N))))
hikHours <- t(sapply(levels(grall$Trail),function(x)
  summary(MaxSecs[Trl==x, Msecs])))/3600
write.csv(x=cbind(
  grall[,length(unique(SurvNum)),keyby=Trail],
  hikHours, hikSegs), file=paste0(srcdir,"output/SurveySummary.csv"))
tmp <- grep(patt="WoErr",names(grall), value=T)[-1] # do not use Tot
write.csv(x=rbindlist(lapply(tmp, function(x)
  grall[,.(.N, Heli=sum(as.numeric(Heli1)-1)/.N,
           Jet=sum(as.numeric(Jet1)-1)/.N,
           Prop=sum(as.numeric(Prop1)-1)/.N),
           keyby=.(round(get(x)/10), Trail)])),
  file=paste0(srcdir,"output/ErgVersusNoted.csv"))
rspnsLbls <- c("very\npleasant", "moderately\npleasant",
                "slightly\npleasant", "neutral", "slightly\nunpleasant",
                "moderately\nunpleasant", "very\nunpleasant")
### Data Checks
# CLEAN THESE UP WITH PRANAV
tmp <- grall[,.(max(SegTot),max(Segment) != .N), by=SurvNum]
tmp <- grall[,.(max(SegTot),max(Segment) != max(SegTot)), by=SurvNum]
summary(grall$SegDur == 0)
### Categorical partitions: simpler plot of LAE histograms by Pleasantness rating
trailLabels <- c("Bright\nAngel", "Hermit", "Widforss")
names(trailLabels) <- levels(grall$Trail)
invWts <- 1/(summary(grall$Pleasant1)/dim(grall)[1])
png(filename=paste(srcdir,"Output/","HeliLaeV6.png",sep=""),
    width=10,height=7,units="in",res=300,bg="white")
opar <- par(no.readonly = T)
par(oma=c(7,13,5,2),mar=rep(0,4),mgp=c(1.5,1,0), mfcol=c(7,3))
bbrks <- grall[, hist(Erg3WoErr, plot=F)$breaks]
bbrks <- bbrks[-c(2,3)]
for(trl in levels(grall$Trail)){
  for (jY in 6:0){
    mPoints <- laePlot(grl=grall[Trail==trl], Pleas=jY+1)
  }
  axis(1, at=apply(mPoints,2,mean),
       labels=c("<30",bbrks[-c(1,length(bbrks))]),
       outer=T, cex.axis=2)
  mtext(trailLabels[trl], outer=T, at=-0.2 + match(trl, levels(grall$Trail))/3)
}
mtext(expression("Helicopter L"[AE]*", dB"),side=1, line=4.5, outer=T, cex=2)
par(opar)
par(oma=c(0,9,0,2))
mmult <- 0.925
mvals <- coefficients(lm(par()$usr[3:4]*mmult ~ c(7,1)))
axis(2, at= 0.9*1/7 + mmult*mvals[1] + mvals[2]*(1:7), outer=T, las=2,
     line=2, labels=rspnsLbls, cex.axis=0.8)
mtext("Trail Segment Pleasantness",side=2,line=7,cex=2, outer=T)
add_legend(x="topright",legend=c("No helicopters noted","Helicopters noted"),
           fill=c("#000000","808080"), cex=1, inset=c(.7925,.005))
dev.off()
grall[Erg3WoErr >= 80 & Pleasant1 > 5, .N, keyby=Heli1]
grall[Pleasant1 == 1 & Erg3WoErr < measurableThreshold,.N, keyby=Heli1]
### Create the Pleasantness table
# Includes Fisher Exact Tests for Measurable LAE contrasts
ctgLbls <- c("No helicopters noted\nNo measurable LAE",
             "No helicopters noted\nMeasurable LAE",
             "Helicopters noted\nNo measurable LAE",
             "Helicopters noted\nMeasurable LAE")
pleasTbl <- grall[,summary(Pleasant1),by=.(Heli1, noHeliErg)]
pleasTbl <- array(pleasTbl$V1,dim=c(7,4),
                  dimnames = list(rev(rspnsLbls),ctgLbls))
rowTsts <- list(c(1,2), c(1,3), c(2,4), c(3,4))
tstrt <- Sys.time()
fshTsts <- future_lapply(X = rowTsts, FUN = function(x){
	return(fisher.test(pleasTbl[, x],simulate.p.value = T, B=1e9)$p.value)
}, future.seed = T)
print(Sys.time() - tstrt)
beep(sound=3)
pleasTbl2 <- rbind(pleasTbl,apply(pleasTbl,2,sum))
pleasTbl2 <- rbind(sweep(pleasTbl2[-8,],2,pleasTbl2[8,],"/"),pleasTbl2[8,])
pleasTbl2 <- rbind(pleasTbl2,fshTsts)
write.csv(x=t(pleasTbl2),
          file=paste(srcdir,"Output/","HeliLaeV1.csv",sep=""))
### Noise Audibility Models
# Critical for the dose-response comparison with Volpe
write.csv(file=paste0(srcdir,"Output/HeardNoise.csv"),
          x = cbind(grall[,.(sum(Erg3WoErr>0)/.N,
                             "Measurable Heli LAE" = sum(Erg3WoErr>0)),by=Trail],
                    grall[,.(sum(Heli1==1)/.N,
                             "Fraction of Segments with Heli=1" =
                               sum(Heli1==1)),by=Trail],
                    grall[,.("Fraction of Heli=1 w/o Heli LAE" =
                               sum(Heli1==1 & Erg3WoErr==0)/sum(Heli1==1),
                             sum(Heli1==1 & Erg3WoErr==0)),by=Trail],
                    grall[,.("Fraction of Measurable Heli LAE with Heli=0" =
                               sum(Heli1==0 & Erg3WoErr>0)/sum(Erg3WoErr>0),
                             sum(Heli1==0 & Erg3WoErr>0)),by=Trail]))
# above are useful summaries
mdlsAud <- makeFormulae(target = "Heli1", vnames =
  c("ErgAvg3", "Erg3WoErr", "SegDur + Erg3WoErr", "cumLaeq3", "cumSEL3"))
mdlsAud <- multiplyFormulae(target = "Heli1", vVector = c("cumLaeq1", "cumSEL1"),
  mdls <- mdlsAud)
# Trail omitted because all data are from Hermit
audVars <- c("Insect1", "Wind1", "Prop1", "Bird1", "NQ", "Thunder1")
mdlsAud <- factorialFormulae("Heli1", audVars, mdlsAud)
mdlsAud <- multiplyFormulae("Heli1", "(1 | SurvNum)", mdlsAud)
mdlsAud <- sapply(mdlsAud, gsub, patt="  ", repl=" ")
names(mdlsAud) <- NULL
trms <- termList(mdlsAud)
nms <- c("Heli1", varList(trms))
uix <- !apply(is.na(grall[,..nms]),1,any) & grall$Trail=="h"
grl <- copy(grall[uix,..nms])
grl[,Hwt:=1/(summary(grl$Heli1)/dim(grl)[1])[as.character(grl$Heli1)]]
grl <- grl[Erg3WoErr!=0]
grl <- data.frame(grl)
# UNWEIGHTED HELI1
parReps <- seq(along=mdlsAud)
mxd <- grep(patt="1 | SurvNum", mdlsAud, fixed = T)
audMods <- vector(mode="list", length=length(mdlsAud))
tstrt <- Sys.time()
# TWO VERSIONS. THIS ONE DOES FIXED AND MIXED
for (ix in parReps[!parReps %in% mxd]){
  print(ix/length(audMods))
  audMods[[ix]] <- glm(formula = mdlsAud[ix], data=grl[, -match("Hwt", names(grl))],
    family="binomial")
}
beep(sound=5)
for (ix in mxd){
  print(ix/length(audMods))
  audMods[[ix]] <- glmer(formula = mdlsAud[ix], data=grl[, -match("Hwt", names(grl))],
    family="binomial", nAGQ=10,
    control = glmerControl(optCtrl=list(maxfun=30000)))
}
beep(sound=5)
# THIS VERSION DOES MIXED EFFECT ONLY
audMods <- lapply(mdlsAud, function(mm)
  glmer(formula=mm, data=grl[, .SD, .SDcols = !"Hwt"],
        family="binomial", nAGQ=10,
        control = glmerControl(optCtrl=list(maxfun=30000))))
print(Sys.time() - tstrt)
audRslts <- modSumOut(audMods, "Heli1")
write.csv(file=paste0(srcdir,"output/AudModels.csv"), audRslts$ModlSumm)
write.csv(file=paste0(srcdir,"output/AudVariables.csv"), audRslts$CoefSumm)
saveRDS(audMods, file=paste0(srcdir,"Output/audMods.RDS"))
beep(sound=2)
### Hermit Heli1 calculation
laePred <- lapply(grep(patt="WoErr", names(grall), value = T), function(l){
  with(grall, {
    LAE <- get(l)
    seq(from = floor(min(LAE[LAE>0])*0.95), to = ceiling(max(LAE)*1.05))
  })
})
names(laePred) <- grep(patt="WoErr", names(grall), value = T)
tmpdat <- copy(grl)
pp <- lapply(laePred[["Erg3WoErr"]], function(j) {
  # calculate predicted probabilities and store in a list
  tmpdat$Erg3WoErr <- j
  predict(audRslts$ModAvg, newdata = tmpdat, type = "response")
})
heliMedline <- sapply(pp, median)
beep(sound=2)
### Other indirect effects of noise
# This did not prove fruitful
airMixed <- T
mdlsErg <- paste0(" ~ ", c("TotErgWoErr", "ErgAvg"))
mdlsErg <- factorialFormulae(target="", vCombos = c("HeliFrac", "JetFrac"),
                             mdls = mdlsErg)
mdlsErg <- c(mdlsErg, sub(patt = "TotErgWoErr", repl = "TotErgWoErr + SegDur",
    x = mdlsErg[grep(patt="TotErg", mdlsErg)]))
mdlsErg <- gsub(patt="  ", repl=" ", mdlsErg)
if(airMixed)
  mdlsErg <- sub(patt="~", repl="~ (1|SurvNum) +", x=mdlsErg)
ancilVars <- names(grall)[sapply(grall,is.factor)][-c(1:5,15,18:24)]
image(cor(apply(as.matrix(grall[, ..ancilVars]),2, as.numeric))) #checking corr
mLineVars <- vector(mode="list", length=length(ancilVars))
names(mLineVars) <- ancilVars
aVars <- varList(termList(mdlsErg))
print(nbrOfWorkers())
tstrt <- Sys.time()
for (v in ancilVars){
  nms <- c(v, aVars)
  uix <- !apply(is.na(grall[,..nms]),1,any)
  grl <- copy(grall[uix,..nms])
  vMdls <- lapply(mdlsErg, function(y) paste0(v, y)) # add the dependent var
  vMdls <- lapply(vMdls, as.formula)
  tstrt <- Sys.time()
  mLineVars[[v]] <- future_lapply(X = vMdls, FUN = function(x, ...) {
    if(airMixed)
      tst2 <- glmer(formula=x, data=grl, family="binomial", nAGQ=10,
                    control = glmerControl(optCtrl=list(maxfun=30000)))
    else
      tst2 <- glm(formula=x, data=grl, family="binomial")
  return(tst2)
  })
print(Sys.time() - tstrt)
}
# was going to compute median conditional probabilities
# noise energy did not substantially affect noting sounds
### The next chunk performs the Hermit only
# used for the Volpe comparison
mdlsH <- makeFormulae("Pleasant1", # tot and heli LAE
             grep(patt="WoErr",names(grall), value=T)[c(1,4)])
mdlsH <- c(mdlsH, sub(patt="~ ",repl="~ SegDur + ",mdlsH)) # add SegDur
mdlsH <- c(mdlsH, sapply(mdlsH[c(2,4)], function(x) paste0(x, ":Heli1")),
           sapply(mdlsH[c(2,4)], function(x) paste0(x, ":cHeli")))
names(mdlsH) <- NULL # 8 models addressing noise levels
# helicopter factors
heliOptions <- c("Heli1", "Heli1 + cHeli")
mdlsH <- c(mdlsH, multiplyFormulae("Pleasant1", heliOptions, mdlsH))
mdlsH <- factorialFormulae(
  target = "Pleasant1",
  vCombos = names(grall)[sapply(grall,is.factor)][-c(1:5,15,18:22)],
  mdls = mdlsH, facDepth = 4)
mdlsH <- sub(patt="~ ",repl='~ (1|SurvNum) + ',mdlsH)
names(mdlsH) <- NULL
nms0 <- termList(mdlsH)
nms0 <- varList(nms0)
nms <- c(nms0, "Pleasant1")
ixHermit <- !apply(is.na(grall[, match(nms,names(grall)),with=F]),1,any) &
  grall$Trail == "h"
print(nbrOfWorkers())
parReps <- seq(along=mdlsH)
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)
  herMods <- future_lapply(parReps, function(x, ...) {
    tst2 <- clmm(formula = mdlsH[x], data=grall[ixHermit, ])
    p(sprintf("x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tst2)
  })
})
print(Sys.time() - tstrt)
hermRslts <- modSumOut(herMods, "Pleasant1")
write.csv(file=paste0(srcdir,"output/herModels.csv"), hermRslts$ModlSumm)
write.csv(file=paste0(srcdir,"output/herVariables.csv"), hermRslts$CoefSumm)
print(order(sapply(herMods,AICc)))
ibest <- which.min(sapply(herMods,AICc))
# HAD TO SHIFT FROM BEST MODEL TO CONDITIONAL MODEL AVERAGED COEFFICIENTS TO OBTAIN A DOSE-RESPONSE
plotting clmm
Pleasant1 ~ ErgA1WoErr + Erg3WoErr + Jet1 + Heli1 + Trail + SegDur + (1|SurvNum))
Pr(y=1) = logit^(-1) {(1|site) + offset + sum(betak*xk)}
Intercept  -7.195
LAE         0.064
%TAud       0.017
PEnHelos    0.017
PEnProps    0.003
Survey HR2  0.080
Importance of calm/peace 0.480
Visited site before      0.118
Adults only              0.250
Watch birds              0.257
Fairyland (BRCA)
Taylor Creek (ZION)
West Rim (ZION)
Grand-view (GRCA)
Hermit (GRCA)
Sperry (GLAC)
Hidden Lake (GLAC) Overall
Average time audible (%)      32 14 35 42 77! 23 19 31
Average helicopter energy (%) 0 0 0 6 80! 86 96 31
Average prop energy (%)       36 55 30 39 12! 11 4 30
Adults only (%)               81 71 87 79 89! 83 79 81
Importance of calm/peace (%)  86 84 89 86 87! 83 84 79
Visited site before (%)       9 11 28 18 13! 16 22 13
Never air tour (%)            88 86 87 90 89! 90 91 89
Watch birds (%)               44 26 30 38 41! 27 28 36
Talk/presentation (%)         3 1 2 5 6! 6 6 3
!!!! REQUIRES HERMIT ONLY ANALYSIS !!!!
### REPLACE THE FOLLOWING WITH MEDIAN MODEL-AVERAGED RESPONSE
# AS DONE WITH HELI1 PREDICTIONS
SplitCoef  <- hermRslts$CoefSumm[1:6,1]
SchoCoef <- hermRslts$CoefSumm[7:dim(hermRslts$CoefSumm)[1],1]
vnames <- varList(termList(
  paste("Pleasant1 ~ ",msTableOutH[msTableOutH["weight"]>1e-6,1][-1])))
vnames <- vnames[-na.omit(
  match(c("ErgA1","Erg3","Trail","Heli1","Erg3WoErr", "SurvNum", "NQ", "cHeli"),vnames))]
# omit the variables that may be changed in SchoDR()
vFactors <- sapply(grall[,..vnames],is.factor)
vmeans <- sapply(lapply(grall[Trail=="h",vnames,with=F],as.numeric),mean,na.rm=T) -
  rep(1,length(vnames))*vFactors
ix <- charmatch(names(vmeans),names(SchoCoef))
MF <- vmeans %*% SchoCoef[ix]
png(filename=paste(srcdir,"Output/","DoseResponseWithAud.png",sep=""),
    width=10,height=7.5,units="in",res=300,bg="white")
par(mar=c(3,4,1,1), mgp=c(1.85,0.75,0))
plot(Lae,rep(0.5,length(Lae)),type="n", log="y", ylim=c(4e-3,1), xlim=range(Lae),
     xlab="LAE in dB", ylab="Probability that pleasantness is\nless than or equal to k")
SchoLines(Helicopt = medline)
dev.off()
png(filename=paste(srcdir,"Output/","DoseResponseHeliContrast.png",sep=""),
    width=10,height=7.5,units="in",res=300,bg="white")
par(mfrow=c(1,2), mar=c(1.5,2.5,2,0), oma=c(2,2,0,2))
plot(Lae,rep(0.5,length(Lae)),type="n", log="y", ylim=c(4e-3,1), xlim=range(Lae),
     xlab="LAE in dB", ylab="Probability that pleasantness is\nless than or equal to k",
     main="No helicopter noted")
SchoLines(Helicopt = F)
plot(Lae,rep(0.5,length(Lae)),type="n", log="y", ylim=c(4e-3,1), xlim=range(Lae),
     xlab="LAE in dB", ylab="Probability that pleasantness is\nless than or equal to k",
     "Helicopter noted")
SchoLines(Helicopt = T)
mtext("LAE in dB", side=1, line=0.5, outer=T)
mtext("P{pleasantness <= 1:6}", side=2, line=0.5, outer=T) 
dev.off()
### The next chunk performs the all trail analysis
# This takes >6 hours to run on Ansel, single threaded
# 17.5 minutes on MiniF, multithreaded
# looks like 4:04:20 for 12288 models
# 4:49 pm -> 8:53 pm
# 11/29: CHECK THE JET RESULTS IN THE INITIAL PASS
# INCLUDE HELI LAE:HELI1 IN THE INITIAL SET
#  DOES IT PROPAGATE FORWARD?
#  wHAT IS THE SIGN OF HELI LAE: HELI=0?
# UPDATE SECOND STATE MODELING IF HELI LAE:HELI1 PROPAGATES FORWARD
# GET THE NEW VALUES FOR SURVNUM AND UPDATE THAT SECTION
# RECALCULATE THE LATER QT ANALYSIS USING THE A SUBSET OF THE FINAL MODELS
allMdls <- "Pleasant1 ~ (1|SurvNum)"
allMdls <- factorialFormulae(target = "Pleasant1",
                           vCombos = c("TotErgWoErr", "HeliFrac", "JetFrac"),
                           mdls=allMdls) # all F: original modls
allMdls <- c(allMdls, sub(patt = "TotErgWoErr",
                          repl = "TotErgWoErr + SegDur",
                          x = allMdls[grep(patt = "TotErgWoErr", x=allMdls)]))
# 12 models thus far
allMdls <- c(allMdls, sub(patt = "TotErgWoErr",
                          repl = "TotErgWoErr:Trail",
                          x = allMdls[grep(patt = "TotErgWoErr", x=allMdls)]))
# 20 models
names(allMdls) <- NULL
# helicopter factors
acOpts <- c("Heli1", "Heli1 + cHeli", "Heli1 + preHeli")
allMdls <- c(allMdls, multiplyFormulae("Pleasant1", acOpts, allMdls))
acOpts <- c("Prop1", "Prop1 + cProp", "Prop1 + preProp")
allMdls <- c(allMdls, multiplyFormulae("Pleasant1", acOpts, allMdls))
acOpts <- c("Jet1", "Jet1 + cJet", "Jet1 + preJet")
allMdls <- c(allMdls, multiplyFormulae("Pleasant1", acOpts, allMdls))
# 1280 models
allMdls <- gsub(patt="  ", repl=" ", x=allMdls)[-1] #remove random effect only
names(allMdls) <- NULL
nms0 <- varList(termList(allMdls))
nms <- c(nms0, "Pleasant1")
ixgood <- !apply(is.na(grall[, match(nms,names(grall)),with=F]),1,any)
parReps <- seq(along=allMdls)
print(nbrOfWorkers())
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)
  allClmm <- future_lapply(parReps, function(x, ...) {
    tst2 <- clmm(formula = allMdls[x], data=grall[ixgood, ])
    p(sprintf("x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tst2)
  })
})
print(Sys.time() - tstrt)
saveRDS(allClmm, file=paste0(srcdir,"Output/allClmm.RDS"))
allResults1 <- modSumOut(allClmm, "Pleasant1")
write.csv(file=paste0(srcdir,"output/allClmmMdls.csv"), allResults1$ModlSumm)
write.csv(file=paste0(srcdir,"output/allClmmCoef.csv"), allResults1$CoefSumm)
save(allClmm, file=paste0(srcdir,"output/allClmm1.RData"))

# use the models with weight > 1%
allMdls2 <- allResults1$ModlSumm[5+(
  which(allResults1$ModlSumm$weight[6:1000]>0.01)),1]
catgOptions <- sort(names(grall)[
  sapply(grall, is.factor)][
    -c(1, 7, 11, 15, 18:20, 22:28)])
allMdls2 <- factorialFormulae("Pleasant1",
                           catgOptions,
                           allMdls2, facDepth = 3)
allMdls2 <- gsub(patt="  ", repl=" ", x=allMdls2)
allMdls2 <- sub(patt="$", repl=" + (1|SurvNum)", allMdls2)
nms0 <- varList(termList(allMdls2))
nms <- c(nms0, "Pleasant1")
ixgood <- !apply(is.na(grall[, match(nms,names(grall)),with=F]),1,any)
print(nbrOfWorkers())
parReps <- seq(along=allMdls2)
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)
  allClmm2 <- future_lapply(parReps, function(x, ...) {
    tst2 <- clmm(formula = allMdls2[x], data=grall[ixgood, ])
    p(sprintf("x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tst2)
  })
})
print(Sys.time() - tstrt)
saveRDS(allClmm2, file=paste0(srcdir,"Output/allClmm2.RDS"))
allResults2 <- modSumOut(allClmm2, "Pleasant1")
write.csv(file=paste0(srcdir,"output/allClmmMdls2.csv"), allResults2$ModlSumm)
write.csv(file=paste0(srcdir,"output/allClmmCoef2.csv"), allResults2$CoefSumm)
}
### Effects of cumulative exposure to helicopter noise.
# Could create 4x7 matrices for each level of cHeli: Heli1 x startHeli
# y-axis ticks using relative jumps between categories based on clmm results
# 2 lines - One for quiet start, one for not quiet start
# 2 options - one with just means, one with means + whiskers (or some other spread representation)
grall[ixgood, ltntScr:= latentPred(hhmods[[ibest]])]
# cHeli must be a factor here !!!!!
bpl <- boxplot(ltntScr ~ cHeli + Heli1 + HeliFirst, data=grall, plot=F)
with(bpl,{ # all four lines
  plot(stats[3,], type="n", xlab="number of segments with helicopter noted",
       ylab="median segment latent score", xlim=c(0,5))
  for (cv in c(sapply(c("0","1"),paste,paste(".",c("0","1"),sep=""),sep=""))){
    ix <- substr(names,3,5)==cv
    lines(as.numeric(substr(names[ix],1,1)),stats[3,ix],
          pch=c("o","H")[as.numeric(substr(cv,1,1)) + 1], type="b",
          lty=1+as.numeric(substr(cv,3,3)))
  }
  mtext("more unpleasant",side=2,line=2,at=3,cex=0.8)
  mtext("less unpleasant",side=2,line=2,at=-2,cex=0.8)
  legend(x="topleft",legend=c("No","Yes"),
         pch=c("o","H"), title="Helicopter noted in this segment")
  legend("bottomright",legend=c("No","Yes"), lty=c(1,2),
         title="Helicopter noted in the first segment")
})
with(bpl,{ # two lines
  opar <- par(no.readonly = T)
  par(mgp = c(3.5, 0.75, 0), mar=c(5,5,1,1))
  plot(stats[3,], type="n", xlab="cumulative number of segments with helicopter noted",
       ylab="median segment latent score with helicopter noted", xlim=c(.9,4.1), ylim=c(-5,0.1),
       xaxs="r",yaxs="i", axes=F, cex.lab=2)
  axis(1, at=1:4, cex.axis=1.333)
  axis(2, cex.axis=1.333)
  for (cv in 0:1){
    ix <- substr(names,3,5)==paste("1.",cv,sep="") &
      as.numeric(substr(names,1,1)) < 5
    lines(as.numeric(substr(names[ix],1,1)),-stats[3,ix],
          type="l", lty=1+cv)
    lines(x=c(sapply(as.numeric(substr(names[ix],1,1))+(cv-0.5)/40,rep,3)),
          y=c(rbind(-stats[c(2,4),ix],NA)),
          lty=1+cv)
    text(x=as.numeric(substr(names[ix],1,1))+(cv-0.5)/5,
         y=-stats[3,ix]+(cv-0.5)/2.5,
         labels=paste("n=",n[ix],sep=""),
         cex=1.5)
  }
  mtext("less pleasant",side=2,line=1.75,at=-4.5,cex=1.333)
  mtext("more pleasant",side=2,line=1.75,at=-0.5,cex=1.333)
  legend("topleft",legend=c("No","Yes"), lty=c(1,2),
         title="Helicopter noted in the first segment", cex=2)
  par(opar)
})
hist(-grall[ixgood & Heli1==1 & cHeli==1 & HeliFirst==0,ltntScr],
     xlab="segment latent score", col=rgb(0,0,1,0.5), xlim=c(-5.5,1.5),
     main="", freq=F, breaks=10)
hist(-grall[ixgood & Heli1==1 & cHeli>=2 & HeliFirst==0,ltntScr],
     col=rgb(1,0,0,0.5), xlim=c(-5.5,1.5),add=T, freq=F, breaks=10)

### End Of Hike
# Plot combinations of segment pleasantnesses versus EoH pleasantness
# 2 combinations - last-worst mean (Kahneman), all segments mean
# fit a mixed effect model using first, last, and worst latent variable scores
grall[,lastSeg := (Segment==max(Segment)),by=SurvNum]
axCex <- 1.2
# mean latent score
#svg(filename="D:/Schomer/PranavData/Output/EohBoxplots.svg", width=7, height=9.5)
CairoSVG(filename="D:/Schomer/PranavData/Output/EohBoxplots.svg", width=7, height=9.5)
par(mfrow=c(4,1), mar=c(1,4,0,1), oma=c(4,0,1,0), mgp=c(2.5, 0.67, 0))
boxplot(grall[ixgood,-mean(ltntScr),by=SurvNum]$V1 ~
          grall[ixgood, unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="mean segment latent values")
axis(2)
# mean segment pleasantness
boxplot(grall[ixgood,mean(as.numeric(Pleasant1)),by=SurvNum]$V1 ~
          grall[ixgood, unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F,frame.plot=T, cex.lab=axCex,
        ylab="mean segment pleasantness")
axis(2)
# Kahnemann latent summary
tmp1 <- grall[ixgood,.(Kahn = -(min(ltntScr) + ltntScr[lastSeg])/2), keyby=SurvNum]
tmp2 <- grall[ixgood, .(Peoh = unique(PleasantEOH)), keyby=SurvNum]
with(tmp2[tmp1], boxplot(Kahn ~ Peoh,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="Kahnemann summary latent values"))
axis(2)
# Kahnemann pleasantness summary
tmp1 <- grall[ixgood,.(Kahn = (min(as.numeric(Pleasant1)) + as.numeric(Pleasant1[lastSeg]))/2), keyby=SurvNum]
tmp2 <- grall[ixgood, .(Peoh = unique(PleasantEOH)), keyby=SurvNum]
with(tmp2[tmp1], boxplot(Kahn ~ Peoh,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="Kahnemann summary pleasantness"))
axis(2)
axis(1, outer=T)
mtext(text="end of hike pleasantness", side=1, outer=T, line=2.5)
dev.off()
# due diligence
axCex <- 1
#svg(filename="D:/Schomer/PranavData/Output/EohBoxSurplus.svg", width=7, height=9.5)
cairo_pdf(filename="D:/Schomer/PranavData/Output/EohBoxSurplus.pdf", width=7, height=9.5)
par(mfrow=c(5,1), mar=c(1,4,0,1), oma=c(4,0,1,0), mgp=c(2.5, 0.67, 0))
boxplot(grall[,Pleasant1[lastSeg],by=SurvNum]$V1 ~
          grall[,unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="last segment pleasantness")
axis(2)
boxplot(grall[,min(Pleasant1),by=SurvNum]$V1 ~
          grall[,unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="minimum pleasantness")
axis(2)
boxplot(grall[,1/mean(1/as.numeric(Pleasant1)),by=SurvNum]$V1 ~
          grall[,unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="harmonic mean pleasantness")
axis(2)
boxplot(grall[,10^mean(log10(as.numeric(Pleasant1))),by=SurvNum]$V1 ~
          grall[,unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="geometric mean pleasantness")
axis(2)
alph <- 1/sqrt(2)
boxplot(grall[,sum(as.numeric(Pleasant1)*alph^(Segment-max(Segment)))/
                sum(alph^(Segment-max(Segment))),
              by=SurvNum]$V1 ~ grall[,unique(PleasantEOH),by=SurvNum]$V1,
        xlab="", axes=F, frame.plot=T, cex.lab=axCex,
        ylab="decay weighted mean pleasantness")
axis(2)
axis(1, outer=T)
mtext(text="end of hike pleasantness", side=1, outer=T, line=2.5)
dev.off()
### predictions of EOH Pleasantness and Natural Sounds
grvlst <- grall[, max(Segment), by=SurvNum]
names(grvlst)[2] <- "Segment"
grvlst <- merge(grvlst,grall[,c("SurvNum","SegDur","Pleasant1","Segment"),with=F],
                 by.x=c("SurvNum","Segment"),by.y=c("SurvNum","Segment"))
grvlst <- merge(grvlst,grall[, sum(SegDur,na.rm=T), by=SurvNum],by.x="SurvNum",by.y="SurvNum")
grvlst <- merge(grvlst,grall[, min(Pleasant1,na.rm=T), by=SurvNum],by.x="SurvNum",by.y="SurvNum")
grvlst <- merge(grvlst,grall[, max(Pleasant1,na.rm=T), by=SurvNum],by.x="SurvNum",by.y="SurvNum")
grvlst <- merge(grvlst,grall[, mean(as.numeric(Pleasant1),na.rm=T),
                             by=SurvNum],by.x="SurvNum",by.y="SurvNum")
names(grvlst)[2:8] <- c("SegL","LstDur","PleasLast","TotDur","PleasMin","PleasMax","PleasAvg")
grvlst <- merge(grvlst,grall[, sum(as.numeric(Pleasant1)*SegDur,na.rm=T),by=SurvNum],
                by.x="SurvNum",by.y="SurvNum")
grvlst[,PleasWvg:=V1/TotDur]
grvlst[,V1:=NULL]
grvlst <- merge(grvlst,unique(grall[, .SD ,by=SurvNum,.SDcols=c("PleasantEOH","NatSoundEOH")]),
                by.x="SurvNum",by.y="SurvNum")
vmatch <- match("NatSoundEOH",names(grvlst))
uix <- !apply(is.na(grvlst[,-vmatch,with=F]),1,any)
gmdls <- c("PleasantEOH ~ PleasLast",
           "PleasantEOH ~ PleasMin",
           "PleasantEOH ~ PleasMax",
           "PleasantEOH ~ PleasAvg",
           "PleasantEOH ~ PleasWvg")
gmods <- lapply(gmdls,function(mm) glm(mm,data=grvlst[uix,], family="binomial")) #anonymous function workaround for glmer
mdsum <- summary(model.avg(gmods))
capture.output(mdsum,file=paste(srcdir,"Output/","AllTrailPeoh.txt",sep=""))
#for NatSoundEOH
vmatch <- match("PleasantEOH",names(grvlst))
uix <- !apply(is.na(grvlst[,-vmatch,with=F]),1,any)
gmdls2 <- c("NatSoundEOH ~ PleasLast",
           "NatSoundEOH ~ PleasMin",
           "NatSoundEOH ~ PleasMax",
           "NatSoundEOH ~ PleasAvg",
           "NatSoundEOH ~ PleasWvg")
gmods2 <- lapply(gmdls2,function(mm) glm(mm,data=grvlst[uix,], family="binomial")) #anonymous function workaround for glmer
mdsum2 <- summary(model.avg(gmods2))
capture.output(mdsum2,file=paste(srcdir,"Output/","AllTrailNSeoh.txt",sep=""))
### Categorical analysis of segment Heli and Pleasantness
# This has no dependencies on other analyses
# Though it can happen anytime in the script, it takes the longest time to run
# so I moved it to the end. It is thus easier to use the Run All Previous Chunks
# command "\/"
forestReplicates <- 200
vmatch <- names(grall)[sapply(grall, is.factor)]
vmatch <- vmatch[-match(c("HeliFirst", "Pleasant1"), vmatch)]
vmatch <- vmatch[-grep(patt="EOH",x=vmatch)] #omit end of hike (causality)
vmatch <- vmatch[-grep(patt="^Surv",x=vmatch)] #omit survey number
vmatch <- c(vmatch,grep(patt="WoErr",x=names(grall), value = T))
vmatch <- c(vmatch, grep(patt="Avg",x=names(grall), value = T), "SegDur")
vmatch <- c(vmatch, grep("cum", names(grall), value=T))
vmatch <- c(vmatch, grep(patt="^cN", names(grall), value=T))
vmatch <- c(vmatch, grep(patt="^Np", names(grall), value = T), "Events")
vmatch <- c(vmatch, grep(patt="^pre", names(grall), value=T), "cEvents")
vmatch <- c(vmatch, grep(patt="^c[AHJP]", names(grall), value=T), "Age")
# cforest can work with ordered factor dependent variables
uix <- !apply(is.na(grall[,..vmatch]),1,any)
grl <- copy(grall[uix,..vmatch])
Hwt <- 1/(summary(grl$Heli1)/dim(grl)[1])[as.character(grl$Heli1)]
cfctrl <- cforest_control(ntree=500) # 500 trees are the default
tstrt <- Sys.time()
cfHeli <- cforest(Heli1 ~ ., weights=Hwt, controls=cfctrl, data=grl)
print(Sys.time() - tstrt)
tstrt <- Sys.time()
predHeli <- predict(cfHeli)
print(Sys.time() - tstrt)
heliTbl <- table(grl$Heli1, predHeli)
print(round(sum(diag(heliTbl))/sum(heliTbl),2))
tstrt <- Sys.time()
hvImp <- varimp(cfHeli)
print(Sys.time() - tstrt)
hvImp2 <- varimpAUC(cfHeli)
print(Sys.time() - tstrt)
iVars <- unlist(strsplit(gsub(patt="[ ]+\\+[ ]+", repl="+", gsub(patt="\\n", repl="",
	cfHeli@data@formula$input))[[2]], split = "+", fixed = T))
rm(cfHeli)
beep(sound=5)
print(nWorkers <- nbrOfWorkers())
parReps <- 1:(nWorkers*round(forestReplicates/nWorkers)) # 6 hours for 49 replicates
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)
  varIMP <- future_lapply(parReps, function(x, ...) {
    cfHeli <- cforest(Heli1 ~ ., weights=Hwt, control=cfctrl,
                      data=grl)
    tmp <- varimp(cfHeli,nperm=1)
    p(sprintf("Heli1  x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tmp)
  })
})
print(Sys.time() - tstrt)
beep(8)
varIMP2 <- reduce(varIMP,rbind)
meanVarImp <- apply(varIMP2,2,mean)
sdVarImp <- apply(varIMP2,2,sd)
ixx <- order(meanVarImp/sdVarImp,decreasing = T)
heliVimp <- cbind(mean=meanVarImp,sd=sdVarImp,zscore=meanVarImp/sdVarImp)[ixx,]
write.csv(heliVimp,file=paste0(srcdir, "Output/","cf1000HeliVimp.csv"))
heliDmeans <- partitionVarImport(grl, "Heli1", iVars, "Hwt")
heliSigns <- ifelse(sapply(vmatch[-grep(patt="eli", vmatch)], function(x)
  sum(diff(grl[,mean(as.numeric(Heli1)), keyby=x]$V1))) < 0,"-","+")
write.csv(file=
            paste0(srcdir,"Output/","HeliVariableImportance1000.csv"),
          cbind(heliVimp,
                heliDmeans[dimnames(heliVimp)[[1]]],
                heliSigns[dimnames(heliVimp)[[1]]])
)

# Pleasantness next
vmatch <- c(vmatch, grep(patt="^TotAir", names(grall), value = T), "HeliFirst", "Pleasant1")
uix <- !apply(is.na(grall[,..vmatch]),1,any)
grl <- copy(grall[uix,..vmatch])
pWeights <- dim(grl)[1]/summary(grl$Pleasant1)
Pwt <- pWeights[grl$Pleasant1]
parReps <- 1:(nWorkers*round(forestReplicates/nWorkers)) # 3 hours for 1000 replicates on mac mini
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)
  pleasIMP <- future_lapply(parReps, function(x, ...) {
    cfPleas <- cforest(Pleasant1 ~ ., weights = Pwt, data=grl)
    tst2 <- varimp(cfPleas, nperm=1)
    p(sprintf("Pleasant1. x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tst2)
  })
})
print(Sys.time() - tstrt)
saveRDS(pleasIMP, file=paste0(srcdir,"Output/pleasIMP.RDS"))
pleasIMP2 <- reduce(pleasIMP,rbind)
meanVarImp <- apply(pleasIMP2,2,mean)
sdVarImp <- apply(pleasIMP2,2,sd)
ixx <- order(meanVarImp/sdVarImp,decreasing = T)
pleasVimp <- cbind(mean=meanVarImp,sd=sdVarImp,zscore=meanVarImp/sdVarImp)[ixx,]
#########
cfPleas <- cforest(Pleasant1 ~ ., weights = Pwt, data=grl)
iVars <- unlist(strsplit(gsub(patt="[ ]+\\+[ ]+", repl="+", gsub(patt="\\n", repl="",
	cfPleas@data@formula$input))[[2]], split = "+", fixed = T))
pleasDmeans <- partitionVarImport(grl, "Pleasant1", iVars, "Pwt")
pleasSigns <- ifelse(sapply(vmatch, function(x)
  sum(diff(grl[,mean(as.numeric(Pleasant1)), keyby=x]$V1))) < 0,"-","+")
vimpNames <- dimnames(pleasVimp)[[1]]
write.csv(file = paste0(srcdir,"Output/","VariableImportance1000.csv"),
          cbind(pleasVimp, pleasDmeans[vimpNames], pleasSigns[vimpNames],
                heliVimp[match(vimpNames, dimnames(heliVimp)[[1]]),],
                heliDmeans[vimpNames],
                heliSigns[vimpNames]))
### The next chunk performs the QT analysis
hix <- "h"==substring(grall$SurvNum,1,1)
hermerg <- merge(x=grall[hix,
                         ("SNum"):=as.numeric(sub(pattern="^.",replac="",SurvNum))],
                 y=grcaqt,by.x=c("SNum","Date"),by.y=c("Survey","Date"))
hermerg[,("QtP"):=(1-ifelse(Totalseg,BellsSeg/Totalseg,0))]
names(hermerg) <- sub(pattern="\\.x",replacement="",names(hermerg))
vmatch <- c(vmatch, "QtP", "Totalseg")
uix <- !apply(is.na(hermerg[,..vmatch]),1,any)
grl <- copy(hermerg[uix,..vmatch])
pWeights <- dim(grl)[1]/summary(grl$Pleasant1)
Pwt <- pWeights[grl$Pleasant1]
parReps <- 1:(nWorkers*round(5*forestReplicates/nWorkers))
handlers("progress", "beepr")
tstrt <- Sys.time()
with_progress({
  p <- progressor(along = parReps)str
  qtpleasIMP <- future_lapply(parReps, function(x, ...) {
    cfPleas <- cforest(Pleasant1 ~ ., weights = Pwt, data=grl)
    tst2 <- varimp(cfPleas, nperm=1)
    p(sprintf("Pleasant1. x=%g, tdiff=%g", x, Sys.time()-tstrt))
    return(tst2)
  })
})
print(Sys.time() - tstrt)
saveRDS(qtpleasIMP, file=paste0(srcdir,"Output/pleasIMP.RDS"))
qtpleasIMP2 <- reduce(qtpleasIMP,rbind)
meanVarImp <- apply(qtpleasIMP2,2,mean)
sdVarImp <- apply(qtpleasIMP2,2,sd)
ixx <- order(meanVarImp/sdVarImp,decreasing = T)
qtpleasVimp <- cbind(mean=meanVarImp,sd=sdVarImp,zscore=meanVarImp/sdVarImp)[ixx,]
###
cfQtPleas <- cforest(Pleasant1 ~ ., weights = Pwt, data=grl)
iVars <- unlist(strsplit(gsub(patt="[ ]+\\+[ ]+", repl="+", gsub(patt="\\n", repl="",
	cfQtPleas@data@formula$input))[[2]], split = "+", fixed = T))
qtpleasDmeans <- partitionVarImport(grl, "Pleasant1", iVars, "Pwt")
qtpleasSigns <- ifelse(sapply(vmatch, function(x)
  sum(diff(grl[,mean(as.numeric(Pleasant1)), keyby=x]$V1))) < 0,"-","+")
vimpNames <- dimnames(qtpleasVimp)[[1]]
write.csv(file = paste0(srcdir,"Output/","VariableImportanceHermitQt.csv"),
          cbind(qtpleasVimp, qtpleasDmeans[vimpNames], qtpleasSigns[vimpNames])
# look at raw relationship between Pleasantness and QtP
jnk <- boxplot(QtP ~ Pleasant1, data = grl)
text(x=1:7, y=.9, lab=paste0("N=", jnk$n))
title("Quiet techology percentage versus Pleasantness (Hermit)")
cfPleasPred <- predict(cfPleas, newdata=grall)
numFact2Number <- function(x) return(as.numeric(as.character(x)))
grall$pleasResid <- numFact2Number(cfPleasPred) - numFact2Number(grall$Pleasant1)
names(grall[, c("SurvNum", "Date", "pleasResid")])
hermerg[, SurvNum:= as.factor(paste0("h", SNum))]
tst <- merge(hermerg, grall[, c("SurvNum", "Date", "pleasResid")],
	by.x = c("SurvNum", "Date"), by.y = c("SurvNum", "Date"))
jnk <- boxplot(QtP ~ pleasResid, data = tst)
text(x=1:10, y=.9, lab=paste0("N=", jnk$n))
title("Quiet techology percentage versus residual Pleasantness")

