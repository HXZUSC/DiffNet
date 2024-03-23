dm "log; clear;";
options ps=80 ls=90 pageno=1 nodate formdlim='-' notes threads;
title;
ODS HTML CLOSE;
ODS HTML;

libname rawdata "C:\Research_Networks\Data";


proc iml;
start lsobj(beta, y, x);
	n=nrow(y); 
   	score=x`*(y-x*beta)/n; 
	hh=0; 
	do i=1 to n;
		lof=x[i,]`*(y[i]-x[i,]*beta)-score; 
		hh=hh+lof*lof`;
    end;
	if (min(vecdiag(hh))>1e8) then do;
		sic=1e8; goto zou;
	end;
	sic=score`*sweep(hh/n)*score; 
	zou:
	return(sic);
finish; 


/* Use the nodewise-parent-selection method in Huang and Zhang (2021) to select parents for each node */
start EstDAG(lambda, allx, bigBini0, mark) global(maxit, small, small2, scada);
	NoNode=ncol(allx); 
	bigBnow=bigBini0; itno=0; absdiff=10; 
	do while (absdiff>small2 & itno<=maxit);
		bigBlast=bigBnow; itno=itno+1;
 
		do j=1 to NoNode;
			ignorej=loc((1:NoNode)^=j);
			betanow=bigBnow[, j];
			
			if max(abs(betanow))=0 then do;
				rc=-1; goto doneold; 
			end; 

			whichrow=loc(mark[, j]=1);
			n=sum(mark[,j]);  
			y=allx[whichrow, j]; y=y-y[:];
			
			label=loc(betanow^=0);
			betanow=betanow[label];
			d=ncol(label);
			
			x=allx[whichrow, label]; x=x-x[:,];

			absdiff_in=10; itno_in=0; rc=0;
		    do while (absdiff_in>small2 & itno_in<maxit);
				noneg=j(d, 1, 0);
				diff=scada#lambda-abs(betanow);
			    pick=loc(diff>0);
			    if ncol(pick)>0 then noneg[pick]=diff[pick];
				
			    penal=lambda#sign(betanow)#((abs(betanow)<=lambda)+(abs(betanow)>lambda)#noneg/((scada-1)#lambda));
			    siglam=diag(penal/abs(betanow));
				hess=-x`*x/n-siglam;
			    score=x`*(y-x*betanow)/n-penal;
			    
		        if (abs(det(hess))>small2) then do;
		            parmest=betanow-inv(hess)*score;
		        	absdiff_in=max(abs(parmest-betanow)); 
					itno_in=itno_in+1;
		            
		            drop=loc(abs(parmest)<small);
		            notdrop=loc(abs(parmest)>=small);

		            if (ncol(drop)>0 & ncol(notdrop)>0) then do;
		                parmest=parmest[notdrop];
		                x=x[, notdrop];
						label=label[notdrop];
		                d=nrow(label);
					end;

		            if ncol(notdrop)=0 then do;
		                rc=-1;  /* no predictor chosen */
		                goto doneold;
		            end;

					betanow=parmest;
		        end;
		        else do;
		            rc=-2; 
					goto doneold; /* The estimates in adjacent two steps are not close enough but Hessian is nearly singular. */
		        end;
			end;
		    doneold: 
			if rc=-1 then bigBnow[, j]=0;
			else do;
				bigBnow[label, j]=betanow;
				bigBnow[setdif(1:NoNode, label), j]=0;
			end;
		end;
		absdiff=max(abs(bigBlast-bigBnow));
	end;
	return(bigBnow); 
finish;

/* Compute PI and DISC scores after estimating two DAGs */
start Find2score(PIscore, disc, tophowmany, allx1, allx2, bigBnow1, bigBnow2, randomseed) 
		global(split, obssize1, obssize2, mark1, mark2, cond1_idx, cond2_idx, pvcutoff); 
		NoNode=nrow(bigBnow1); 
		resids1to2=j(obssize2[<>], NoNode, 0); resids2to1=j(obssize1[<>], NoNode, 0); 
		resids1to1=resids2to1; resids2to2=resids1to2; 
		do j=1 to NoNode;
			whichrow1=loc(mark1[, j]=1); whichrow2=loc(mark2[, j]=1);
			
			/* Assuming G1 structure */
			whichcol=loc(bigBnow1[, j]^=0); 
			d=ncol(whichcol);
			
			if (d>0) then do;
				yx=allx2[whichrow2, j]||allx2[whichrow2, whichcol];
				yx=yx-yx[:,]; 
				y2=yx[, 1]; x2=yx[, 2:(d+1)];
				resids1to2[1:obssize2[j], j]=y2-x2*ginv(x2`*x2)*x2`*y2;
				
				yx=allx1[whichrow1, j]||allx1[whichrow1, whichcol];
				yx=yx-yx[:,]; 
				y1=yx[, 1]; x1=yx[, 2:(d+1)];
				estB=ginv(x1`*x1)*x1`*y1;
				resids1to1[1:obssize1[j], j]=y1-x1*estB;
			end;
			else do; 
				y=allx2[whichrow2, j];
				resids1to2[1:obssize2[j], j]=y-y[:];

				y=allx1[whichrow1, j];
				resids1to1[1:obssize1[j], j]=y-y[:];
			end;	

			/* Assume G2 structure */
			whichcol=loc(bigBnow2[, j]^=0); 
			d=ncol(whichcol);
			
			if (d>0) then do;
				yx=allx1[whichrow1, j]||allx1[whichrow1, whichcol];
				yx=yx-yx[:,]; 
				y1=yx[, 1]; x1=yx[, 2:(d+1)];
				resids2to1[1:obssize1[j], j]=y1-x1*ginv(x1`*x1)*x1`*y1;
				
				yx=allx2[whichrow2, j]||allx2[whichrow2, whichcol];
				yx=yx-yx[:,]; 
				y2=yx[, 1]; x2=yx[, 2:(d+1)];
				estB=ginv(x2`*x2)*x2`*y2;
				resids2to2[1:obssize2[j], j]=y2-x2*estB;
			end;
			else do; 
				y=allx1[whichrow1, j];
				resids2to1[1:obssize1[j], j]=y-y[:];

				y=allx2[whichrow2, j];
				resids2to2[1:obssize2[j], j]=y-y[:];
			end;				
		end;

		/* Randomly split resids into two halves corresponding to two sets of experimental conditions under which node j is not intervened */
		pvs1to2=j(NoNode, 3, 1); pvs2to1=j(NoNode, 3, 1); 
		pvs1to1=j(NoNode, 3, 1); pvs2to2=j(NoNode, 3, 1); 
		disc=j(NoNode, 1, 1);
		PIscore=0; tophowmany=0;
		do sp=1 to split;
			do j=1 to NoNode;
				samsize1=floor(obssize2[j]/2); samsize2=obssize2[j]-samsize1;
				set=j(obssize2[j], 1, 2); 
				cond_idx_inj=cond2_idx[loc(mark2[, j]=1)];
				nocond=ncol(unique(cond_idx_inj));
				if nocond>1 then do;
					firsthalf=floor(nocond/2); 
					call randseed(randomseed+sp+j);
					twoset=ranperm(unique(cond_idx_inj));

					do expcond=1 to firsthalf;
						thiscond=twoset[expcond];
						set[loc(cond_idx_inj=thiscond)]=1; 
					end;
					
					
					sample1=resids1to2[loc(set=1), j]; sample2=resids1to2[loc(set=2), j]; 
					howcomp=MeanVartest(sample1, sample2, samsize1, samsize2);
					pvs1to2[j, ]=howcomp;

					sample1=resids2to2[loc(set=1), j]; sample2=resids2to2[loc(set=2), j]; 
					howcomp=MeanVartest(sample1, sample2, samsize1, samsize2);
					pvs2to2[j, ]=howcomp;
				end;
				else do;
					pvs1to2[j, 1]=888; pvs2to2[j, ]=888;
				end;


				samsize1=floor(obssize1[j]/2); samsize2=obssize1[j]-samsize1;
				set=j(obssize1[j], 1, 2); 
				cond_idx_inj=cond1_idx[loc(mark1[, j]=1)];
				nocond=ncol(unique(cond_idx_inj));
				if nocond>1 then do;
					firsthalf=floor(nocond/2); 
					call randseed(randomseed*100+99+sp+j);
					twoset=ranperm(unique(cond_idx_inj));

					do expcond=1 to firsthalf;
						thiscond=twoset[expcond];
						set[loc(cond_idx_inj=thiscond)]=1; 
					end;
					
					sample1=resids2to1[loc(set=1), j]; sample2=resids2to1[loc(set=2), j]; 
					howcomp=MeanVartest(sample1, sample2, samsize1, samsize2);
					pvs2to1[j, ]=howcomp;
					
				    sample1=resids1to1[loc(set=1), j]; sample2=resids1to1[loc(set=2), j]; 
					howcomp=MeanVartest(sample1, sample2, samsize1, samsize2);
					pvs1to1[j, ]=howcomp;
				end;
				else do;
					pvs2to1[j, 1]=888; pvs1to1[j, ]=888;
				end;

				if sp=1 then do;
					commondeno=resids1to1[,j]`*resids1to1[,j]+resids2to2[,j]`*resids2to2[,j];
					disc[j]=(resids2to1[,j]`*resids2to1[,j]+resids1to2[,j]`*resids1to2[,j])/commondeno;
				end; 
			end;
			PIscore=PIscore+(exp(-pvs1to2[, 3])<>exp(-pvs2to1[, 3]))/(exp(-pvs1to1[, 3])<>exp(-pvs2to2[, 3]));
			tophowmany=tophowmany+(sum(pvs1to2[, 3]<pvcutoff))<>(sum(pvs2to1[, 3]<pvcutoff));
		end;
		PIscore=PIscore/split;
		tophowmany=ceil(tophowmany/split);
finish; 

/* Obtain a p-value matrix for the unpenalized estimated regression coefficients obtained from corrected score method */
start Getpv(GraphEst, allx, mark);
	NoNode=ncol(allx); totn=nrow(allx);  
	pvmat=j(NoNode, NoNode, -8); 
	do j=1 to NoNode;
		whichcol=loc(GraphEst[, j]^=0); d=ncol(whichcol); 
		if (d>0) then do;
			whichrow=loc(mark[, j]=1);
			nall=sum(mark[,j]);
		
			yx=allx[whichrow, j]||allx[whichrow, whichcol];
			yx=yx-yx[:,]; 
			y=yx[, 1]; x=yx[, 2:(d+1)]; 

			Bhat=ginv(x`*x)*x`*y; 

			meatmat=0; breadmat=0; 
			do i=1 to nall;  
			    score=x[i, ]`*(y[i]-x[i,]*Bhat);
				hess=-x[i,]`*x[i,];
			    meatmat=meatmat+score*score`;
				breadmat=breadmat+hess;
			end;
			meatmat=meatmat/nall; breadmat=breadmat/nall;
			ainv=ginv(breadmat);

			varbhat=ainv*meatmat*ainv`/nall; 
			tval=Bhat/sqrt(vecdiag(varbhat));
			pvmat[whichcol, j]=2*CDF('T', -abs(tval), nall-d);
		end;		
	end;
	return(pvmat);  
finish;


/* Delete cycles in an initial graph estimate based on p-values */
start TopSort(GraphEst, pvmat); 
	if (norm(GraphEst)=0) then goto emptygraph;

	NoNode=ncol(graphest);
	noid=(1:NoNode); topo=0;

	do while (ncol(topo)=1);
		anyrt=0;
		do j=1 to NoNode;
			if (norm(GraphEst[, j], "LInf")=0) then do;
				anyrt=anyrt+1;
				topo=topo||j; noid=noid[loc(noid^=j)]; 
			end;	
		end;
		
		if (anyrt=0) then do;
			weakest=loc(pvmat=max(pvmat[loc(GraphEst^=0)]));
			GraphEst[weakest]=0;
			pvmat[weakest]=-1;
		end;
	end;
	
	topo=topo[2:ncol(topo)]`; remnd=nrow(noid); 
	if (remnd=1) then topo=topo||noid;
	temp=GraphEst;
	do while (remnd>1);
		temp=GraphEst[noid, noid]; 
		temp_noid=noid;
		anyrt=0;
		do j=1 to remnd;
			thisnode=temp_noid[j];
			if (norm(temp[, j], "LInf")=0) then do;
				topo=topo||thisnode; 
				anyrt=anyrt+1;
				still=loc(noid^=thisnode);
				if (ncol(still)>0) then noid=noid[still];
			end;	
		end;
		if (anyrt=0) then do;
			weakest=loc(pvmat=max(pvmat[loc(GraphEst^=0)]));
			GraphEst[weakest]=0;
			pvmat[weakest]=-1;
		end;
		remnd=nrow(noid);
		if (remnd=1 & ncol(topo)<NoNode) then topo=topo||noid;
	end;

	emptygraph:
	return(GraphEst);
finish;

/* Compute p-values needed to compute PI scores */
start MeanVarTest(sample1, sample2, samsize1, samsize2) global(VarpvCt); 
	sampvar1=var(sample1); sampvar2=var(sample2);
	
	larger=sampvar1<>sampvar2; 
	smaller=sampvar1><sampvar2;
	if larger>sampvar2 then do; 
		nlarge=samsize1; nsmall=samsize2;
	end; 
	else do; 
		nlarge=samsize2; nsmall=samsize1;
	end; 
	pvar=cdf("F", smaller/larger, nsmall-1, nlarge-1)+sdf("F", larger/smaller, nlarge-1, nsmall-1);

	if (pvar<VarpvCt) then do; /* two-sample t test without assuming equal variance */
		sumvar=sampvar1/samsize1+sampvar2/samsize2;
		df=sumvar**2/((sampvar1/samsize1)**2/(samsize1-1)+(sampvar2/samsize2)**2/(samsize2-1));
		tstat=(sample1[:]-sample2[:])/sqrt(sumvar);
	end; 
	else do; /* two-sample t test assuming equal variance */
		df=samsize1+samsize2-2; 
		poolvar=((samsize1-1)*sampvar1+(samsize2-1)*sampvar2)/df;
		tstat=(sample1[:]-sample2[:])/sqrt(poolvar*(1/samsize1+1/samsize2));
	end;	
	pmean=2*sdf("T", abs(tstat), df);

	lower=pmean><pvar; 

	return(pmean||pvar||lower);
finish; 

/* Benjamini-Hochberg procedure: input original p-values, output the node indices with significant p-values after BH adjustment */
start BHpv(pvs) global(fdr); 
	m=max(nrow(pvs), ncol(pvs)); 
	ids=do(1, m, 1)`;
	tag=ids||pvs;
	call sort(tag, 2);
	crt=fdr*(ids/m); 
	lower=loc(tag[, 2]<crt);
	if ncol(lower)>0 then do;
		cutoff=lower[ncol(lower)];
		claim=tag[, 1][1:cutoff];
		return(claim); 
	end;
	else do;
		return(-1); /* This means there is no significant p-value. */
	end;
finish; 

/* Find driver nodes after identifying differential nodes, given two estimated DAGs */
start FindDriver(DiffNode) global(NoNode, bigBnow1, bigBnow2);
	tophowmany=max(nrow(DiffNode), ncol(DiffNode)); 
	driver=j(tophowmany, NoNode, 0);
	do k=1 to tophowmany;
		child=DiffNode[k]; 
		pa1=loc(bigBnow1[, child]^=0);
		pa2=loc(bigBnow2[, child]^=0);
		nopa1=ncol(pa1); nopa2=ncol(pa2); 

		if ((nopa1><nopa2)>0) then do;
			discrep=setdif(union(pa1, pa2), xsect(pa1, pa2)); 
			if ncol(discrep)>0 then driver[k, discrep]=1;
		end;
		else do; 
			if (nopa1=0 & nopa2>0) then driver[k, pa2]=1; 
			if (nopa2=0 & nopa1>0) then driver[k, pa1]=1; 
		end;
	end;
	touched=loc(driver[+, ]>0);
	claimdriv=ncol(touched);
	if claimdriv>0 then return(touched);
	else return(-1); /* This means there is no drive node. */
finish;


/*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*/
use rawdata.all9; read all into alldata; close rawdata.all9;

/*~~~~~~~~~~~~~~~~~~ pick out only nodes that have both observational data and interventional data ~~~~~~~~~~~~~~~~~~*/
GoodNodes=loc((alldata[, 1:11])[+, ]<nrow(alldata));
print GoodNodes;

alldata=alldata[, GoodNodes||(GoodNodes+11)];
NoNode=ncol(GoodNodes); 
print "No. of nodes with both observational data and interventional data:" NoNode; 


/* There are 9 experimental conditions in this data. */
intervene_size={853, 902, 911, 723, 810, 799, 848, 913, 707};
exp_cond=nrow(intervene_size); 
stacknj=cusum(intervene_size);

/*~~~~~~~~~~~~~~~~~~ only use part of the full data ~~~~~~~~~~~~~~~~~~*/
reduct=6; 
do re=1 to reduct; 
	newintervene_size=round(intervene_size/2);
	newstacknj=cusum(newintervene_size);
	newalldata=alldata[1:newintervene_size[+], ];
	do itv=1 to exp_cond; 
		if itv=1 then do;
			call randseed(itv+re+987876);
			permindex=ranperm(intervene_size[itv]);

			messed=alldata[permindex, ];
			newalldata[1:newintervene_size[1], ]=messed[1:newintervene_size[1], ];
		end;	
		else do;
			call randseed(itv+re+677);
			permindex=ranperm(intervene_size[itv])+stacknj[itv-1];

			messed=alldata[permindex, ];
			newalldata[(newstacknj[itv-1]+1):newstacknj[itv], ]=messed[1:newintervene_size[itv], ];
		end;
	end;
	alldata=newalldata; 
	intervene_size=newintervene_size;
	exp_cond=nrow(intervene_size); 
	stacknj=cusum(intervene_size);
end;

/*----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/*~~~~~~~~~~~~~~~~~~ if I want to keep the original (part of) full data and then create another data of similar structure by manipulating the full data, do the following ~~~~~~~~~~~~~~~~~~*/
mark1=alldata[, 1:NoNode];
allx1=alldata[, (NoNode+1):2*NoNode]; 
mark2=mark1;
noise=2*normal(j(nrow(allx1), ncol(allx1), 4656));
allx2=allx1+noise; 


/* standardize each column */
eachmean=mean(allx1); eachstd=std(allx1);
allx1=(allx1-eachmean@j(nrow(allx1), 1, 1))/(eachstd@j(nrow(allx1), 1, 1));
eachmean=mean(allx2); eachstd=std(allx2);
allx2=(allx2-eachmean@j(nrow(allx2), 1, 1))/(eachstd@j(nrow(allx2), 1, 1));


messobs1=3; /* the node whose observational data I will mess up in the second data set */
messint=2; /* the node whose interventional data I will mess up in the second data set */
allx2[loc(mark2[, messobs1]=1), messobs1]=median(allx2[loc(mark2[, messobs1]=1), messobs1])+normal(j(ncol(loc(mark2[, messobs1]=1)), 1, 5656));
messintsch=1;
allx2[loc(mark2[, messint]=0), messint]=median(allx2[loc(mark2[, messintsch]=1), messintsch])+normal(j(ncol(loc(mark2[, messint]=0)), 1, 656));

intervene_cond1=intervene_size;
intervene_cond2=intervene_cond1;
stacknj1=cusum(intervene_cond1);
stacknj2=cusum(intervene_cond2);

do itv=1 to exp_cond; 
	if itv=1 then do;
		cond1_idx=j(intervene_cond1[1], 1, 1);
		cond2_idx=j(intervene_cond2[1], 1, 1);
	end;	
	else do;
		cond1_idx=cond1_idx//j(intervene_cond1[itv], 1, itv);
		cond2_idx=cond2_idx//j(intervene_cond2[itv], 1, itv);
	end;
end;


sampsize1=nrow(allx1); sampsize2=nrow(allx2);
print sampsize1 sampsize2;

diagIdx = do(1, NoNode*NoNode, NoNode+1);	
optn=(NoNode-1)||0;

maxit=100; small=1e-3; small2=1e-4; 
scada=3.7; 
varpvct=0.05; fdr=0.05;

pvcutoff=0.025;

rt=0.1;
lambmax=0.8;
lambmin=lambmax*rt;
m=100; 
aa=0.1; scada=3.7; scada1=scada-1;
q=rt**(1/(m-1));
split=2; 
permno=300; 

/**~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Estimate B1 & B2 ~~~~~~~~~~~~~~~~~~~~~~~~~~**/
NoObsInt=nrow(allx1); 
NoObs1=j(NoNode, 1, 0); NoObs2=NoObs1; 
obssize1=j(NoNode, 1, 0); obssize2=obssize1;
bigBini1=j(NoNode, NoNode, 0); bigBini2=bigBini1; 

/* Obtain initial estimates of B1 and B2 */
do j=1 to NoNode; 
	ignorej=loc((1:NoNode)^=j);
	whichrow=loc(mark1[, j]=1);
	NoObs1[j]=sum(mark1[,j]);  
	obssize1[j]=sum(mark1[, j]); obssize2[j]=sum(mark2[, j]);
			
	x=allx1[whichrow, ignorej];
	y=allx1[whichrow, j];
	y=y-y[:]; x=x-x[:, ]; 
	bigBini1[ignorej, j]=inv(x`*x)*x`*y;

	whichrow=loc(mark2[, j]=1);
	NoObs2[j]=sum(mark2[,j]);
	x=allx2[whichrow, ignorej];
	y=allx2[whichrow, j];
	y=y-y[:]; x=x-x[:, ]; 
	bigBini2[ignorej, j]=inv(x`*x)*x`*y;
end;

bicpen=(log(NoObs1)/NoObs1)[:];
bicpen2=(log(NoObs2)/NoObs2)[:];

do i=1 to (NoNode-1); 
	do j=i+1 to NoNode;
		if abs(bigBini1[i,j])<=abs(bigBini1[j,i]) then bigBini1[i,j]=0;
		else bigBini1[j,i]=0;

		if abs(bigBini2[i,j])<=abs(bigBini2[j,i]) then bigBini2[i,j]=0;
		else bigBini2[j,i]=0;
	end;
end;

/* Estimate B1 and B2 at a sequence of candidate lambda's */  
lambda1=lambmax; lambda2=lambmax;
do mm=1 to m;
	lambda=lambmax*q**(mm-1); 
	
	bigBnow1=EstDAG(lambda, allx1, bigBini1, mark1); 
	pvmat=Getpv(bigBnow1, allx1, mark1);
	bigBnow1=TopSort(bigBnow1, pvmat);
	
	bigBnow2=EstDAG(lambda, allx2, bigBini2, mark2); 
	pvmat=Getpv(bigBnow2, allx2, mark2);
	bigBnow2=TopSort(bigBnow2, pvmat);
	
	sic1=0; sic2=0;
	do j=1 to NoNode; 
		ignorej=loc((1:NoNode)^=j); 
		whichrow=loc(mark1[, j]=1);
		
		yx=allx1[whichrow, ]; 
		yx=yx-yx[:,];
		y=yx[, j]; x=yx[, ignorej];
		sic1=sic1+lsobj(bigBnow1[ignorej, j], y, x);

		whichrow=loc(mark2[, j]=1);
		
		yx=allx2[whichrow, ]; 
		yx=yx-yx[:,];
		y=yx[, j]; x=yx[, ignorej];
		sic2=sic2+lsobj(bigBnow2[ignorej, j], y, x);
	end;

	if mm=1 then do; 
		smallestsic1=sic1+sum(bigBnow1^=0)#bicpen; 
		sic1=smallestsic1;
		bestB1=bigBnow1;

		smallestsic2=sic2+sum(bigBnow2^=0)#bicpen2; 
		sic2=smallestsic2;
		bestB2=bigBnow2;
	end; 
	else do; 
		sic1=sic1+sum(bigBnow1^=0)#bicpen; 
		if sic1<=smallestsic1 then do;
			smallestsic1=sic1;
			lambda1=lambda;
			bestB1=bigBnow1;
		end;
	
		sic2=sic2+sum(bigBnow2^=0)#bicpen2; 
		if sic2<=smallestsic2 then do;
			smallestsic2=sic2;
			lambda2=lambda;
			bestB2=bigBnow2;
		end;
	end;
end;
bigBnow1=bestB1; bigBnow2=bestB2;
print lambda1 lambda2 bigBnow1 bigBnow2;

/* Compute PI and DISC scores */
randomseed=23435;
run Find2score(PIscore, disc, tophowmany, allx1, allx2, bigBnow1, bigBnow2, randomseed); 
print PIscore disc tophowmany;

if tophowmany>0 then do; 
	keeptrackPI=do(1, NoNode, 1)`||PIscore;
	call sort(keeptrackPI, 2, 2);
	pidiff=keeptrackPI[1:tophowmany, 1];
	print "PI identifies the following differential nodes:" pidiff;

	keeptrackdisc=do(1, NoNode, 1)`||disc;
	call sort(keeptrackdisc, 2, 2); 
	discdiff=keeptrackdisc[1:tophowmany, 1];
	print "DISERCN2-PI identifies the differential nodes:" discdiff;

	pidriv=FindDriver(pidiff);
	discdriv=FindDriver(discdiff);
	if pidriv=-1 then do; 
		print "PI does not identify any driver node.";
	end;
	else do; 
		print "PI identifies the following drive nodes:" pidriv; 
	end;

	if discdriv=-1 then do; 
		print "DISC does not identify any driver node.";
	end;
	else do; 
		print "DISC identifies the following drive nodes:" discdriv; 
	end;
end;
else do; 
	print "PI does not identify any differential node.";
end; 

/* Obtain empirical power based on nonparametric bootstrap */
freq_PI=j(NoNode, 2, 0); freq_disc=j(NoNode, 2, 0); 
do perm=1 to permno; 
	call randseed(7746+perm);
	unitidx=sample(1:intervene_cond1[1]);
	allpermx1=allx1[unitidx, ]; 
	unitidx=sample(1:intervene_cond2[1]);
	allpermx2=allx2[unitidx, ];
	
	do expcond=2 to exp_cond;
		 call randseed(65+perm+expcond);
     	 unitidx=ranperm((stacknj1[expcond-1]+1):stacknj1[expcond]);
		 allpermx1=allpermx1//allx1[unitidx, ]; 
		 unitidx=ranperm((stacknj2[expcond-1]+1):stacknj2[expcond]);
		 allpermx2=allpermx2//allx2[unitidx, ];
	end; 			

	bigBnow1_perm=EstDAG(lambda1, allpermx1, bigBini1, mark1); 
	pvmat=Getpv(bigBnow1_perm, allpermx1, mark1);
	bigBnow1_perm=TopSort(bigBnow1_perm, pvmat);

	bigBnow2_perm=EstDAG(lambda2, allpermx2, bigBini2, mark2); 
	pvmat=Getpv(bigBnow2_perm, allpermx2, mark2);
	bigBnow2_perm=TopSort(bigBnow2_perm, pvmat);
	
	randomseed=134+perm;
	run Find2score(PIscore_perm, disc_perm, tophowmany_perm, allpermx1, allpermx2, bigBnow1_perm, bigBnow2_perm, randomseed); 			

	if tophowmany_perm>0 then do;
		keeptrack=do(1, NoNode, 1)`||PIscore_perm;
		call sort(keeptrack, 2, 2); 
		diffnd=keeptrack[1:tophowmany_perm, 1];
		if ncol(diffnd)>0 then do;
			freq_PI[diffnd, 1]=freq_PI[diffnd, 1]+1; 
			drivnd=FindDriver(diffnd);
			if drivnd^=-1 then freq_PI[drivnd, 2]=freq_PI[drivnd, 2]+1; 
		end;

		keeptrack=do(1, NoNode, 1)`||disc_perm;
		call sort(keeptrack, 2, 2); 
		diffnd=keeptrack[1:tophowmany_perm, 1];
		if ncol(diffnd)>0 then do;
			freq_disc[diffnd, 1]=freq_disc[diffnd, 1]+1; 
			drivnd=FindDriver(diffnd);
			if drivnd^=-1 then freq_disc[drivnd, 2]=freq_disc[drivnd, 2]+1;
		end;
	end;
end;
freq_PI=freq_PI/permno; freq_disc=freq_disc/permno;  
print "Using empirical power:" freq_PI freq_disc; 			


quit;
