dm "log; clear;";
options ps=80 ls=90 pageno=1 nodate formdlim='-' notes threads;
title;
ODS HTML CLOSE;
ODS HTML;
libname out "C:\Research_Networks\Output";


data track;
    t=time(); d=today();
    put 'Time: ' t time9.;
    put 'Date: ' d date9.;
run;

proc iml;
start lsobj(beta, y, x) global(small3);
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

/* Estimate bigB for a sequence of candidate lambda's */ 
start Tuning1(lambda1, bestB1, theorder, lambmax, m, q, allx1, bigBini1) global(NoNode, nj);
	oldnj=nj; nj=nrow(allx1)/NoNode; 
	NoObsInt=nrow(allx1); NoObs=NoObsInt-nj; 
	bicpen1=log(NoObs)/NoObs;
	lambda1=lambmax;
	do mm=1 to m;
		lambda=lambmax*q**(mm-1); 
		
		bigBnow1=findgraph2(lambda, allx1, bigBini1); 
		pvmat=getpv2(bigBnow1, allx1);
		wantall=topsort(bigBnow1, pvmat);
		bigBnow1=wantall[, 1:NoNode];
		theorder=wantall[, (NoNode+1)];
	
		/* using the estimated graph, compute SIC tuning parameter selector (eveluated at the penalized Bhat). */
		sic1=0; 
		do j=1 to NoNode; 
			ignorej=loc((1:NoNode)^=j); 
			if j=1 then whichrow=(nj+1):NoObsInt;
			if (j>1 & j<NoNode) then whichrow=(1:((j-1)#nj))||((j#nj+1):NoObsInt);
			if j=NoNode then whichrow=1:((NoNode-1)#nj);
			
			yw=allx1[whichrow, ]; 
			yw=yw-yw[:,];
			y=yw[, j]; w=yw[, ignorej];
			sic1=sic1+lsobj(bigBnow1[ignorej, j], y, w);
		end;

		if mm=1 then do; 
			smallestsic1=sic1+sum(bigBnow1^=0)#bicpen1; 
			sic1=smallestsic1;
			bestB1=bigBnow1;
		end; 
		else do; 
			sic1=sic1+sum(bigBnow1^=0)#bicpen1; 
			if sic1<=smallestsic1 then do;
				smallestsic1=sic1;
				lambda1=lambda;
				bestB1=bigBnow1;
			end;
		end;
    end;

	nj=oldnj; 
finish;


/* Estimate bigB for a sequence of candidate lambda's */  
start Tuning(lambda1, lambda2, bestB1, bestB2, lambmax, m, q, allx1, allx2, bigBini1, bigBini2) global(NoNode, nj, NoObsInt, bicpen1, bicpen2);
	lambda1=lambmax; lambda2=lambmax;
	do mm=1 to m;
		lambda=lambmax*q**(mm-1); 
		
		bigBnow1=findgraph2(lambda, allx1, bigBini1); 
		pvmat=getpv2(bigBnow1, allx1);
		bigBnow1=topsort(bigBnow1, pvmat)[, 1:NoNode];
		
		bigBnow2=findgraph2(lambda, allx2, bigBini2); 
		pvmat=getpv2(bigBnow2, allx2);
		bigBnow2=topsort(bigBnow2, pvmat)[, 1:NoNode];
		
		/* using the estimated graph, compute SIC tuning parameter selector (eveluated at the penalized Bhat). */
		sic1=0; sic2=0; 
		do j=1 to NoNode; 
			ignorej=loc((1:NoNode)^=j); 
			if j=1 then whichrow=(nj+1):NoObsInt;
			if (j>1 & j<NoNode) then whichrow=(1:((j-1)#nj))||((j#nj+1):NoObsInt);
			if j=NoNode then whichrow=1:((NoNode-1)#nj);
			
			yw=allx1[whichrow, ]; 
			yw=yw-yw[:,];
			y=yw[, j]; w=yw[, ignorej];
			sic1=sic1+lsobj(bigBnow1[ignorej, j], y, w);

			yw=allx2[whichrow, ]; 
			yw=yw-yw[:,];
			y=yw[, j]; w=yw[, ignorej];
			sic2=sic2+lsobj(bigBnow2[ignorej, j], y, w);
		end;

		if mm=1 then do; 
			smallestsic1=sic1+sum(bigBnow1^=0)#bicpen1; 
			sic1=smallestsic1;
			bestB1=bigBnow1;

			smallestsic2=sic2+sum(bigBnow2^=0)#bicpen2; 
			sic2=smallestsic2;
			bestB2=bigBnow2;
		end; 
		else do; 
			sic1=sic1+sum(bigBnow1^=0)#bicpen1; 
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
finish;


/* Use my earlier variable selection code to select parents for each node based on corrected score method with LQA algorithm*/
start findgraph2(lambda, allw, bigBini0) global(nj, threshold, maxit, small, small2, scada);
	pall=ncol(allw); dall=pall-1; totn=nrow(allw); 
	oldnj=nj; nj=totn/pall;
	nall=totn-nj; 
	 
	bigBnow=bigBini0; n=nall; itno=0; absdiff=10; 
	
	do while (absdiff>threshold & itno<=maxit);
		bigBlast=bigBnow; itno=itno+1;
 
		do j=1 to pall;
			ignorej=loc((1:pall)^=j);
			betanow=bigBnow[, j];
			
			if max(abs(betanow))=0 then do;
				rc=-1; goto doneold; 
			end; 

			if j=1 then whichrow=(nj+1):totn; 
			if (j>1 & j<pall) then whichrow=(1:((j-1)#nj))||((j#nj+1):totn);
			if j=pall then whichrow=1:(dall#nj);
			y=allw[whichrow, j]; y=y-y[:];
			
			label=loc(betanow^=0);
			betanow=betanow[label];
			d=ncol(label);
			
			w=allw[whichrow, label]; w=w-w[:,];

			absdiff_in=10; itno_in=0; rc=0;
		    do while (absdiff_in>threshold & itno_in<maxit);
				noneg=j(d, 1, 0);
				diff=scada#lambda-abs(betanow);
			    pick=loc(diff>0);
			    if ncol(pick)>0 then noneg[pick]=diff[pick];
				
			    penal=lambda#sign(betanow)#((abs(betanow)<=lambda)+(abs(betanow)>lambda)#noneg/((scada-1)#lambda));
			    siglam=diag(penal/abs(betanow));
				hess=-w`*w/n-siglam;
			    score=w`*(y-w*betanow)/n-penal;
			    
		        if (abs(det(hess))>threshold) then do;
		            parmest=betanow-inv(hess)*score;
		        	absdiff_in=max(abs(parmest-betanow)); itno_in=itno_in+1;
		            
		            drop=loc(abs(parmest)<small);
		            notdrop=loc(abs(parmest)>=small);

		            if (ncol(drop)>0 & ncol(notdrop)>0) then do;
		                parmest=parmest[notdrop];
		                w=w[, notdrop];
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
				bigBnow[setdif(1:pall, label), j]=0;
			end;
		end;
		absdiff=max(abs(bigBlast-bigBnow));
	end;
	nj=oldnj;
	return(bigBnow); 
finish;

/* Obtain a p-value matrix for the unpenalized estimated regression coefficients obtained from corrected score method */
start getpv2(graphest, allw) global(nj);
	pall=ncol(allw); totn=nrow(allw); 
	oldnj=nj; nj=totn/pall; 
	nall=totn-nj;

	pvmat=j(pall, pall, -8); 
	do j=1 to pall;
		whichcol=loc(graphest[, j]^=0); d=ncol(whichcol); 
		if (d>0) then do;
			if (j>1 & j<pall) then whichrow=(1:((j-1)#nj))||((j#nj+1):totn); 
			if j=1 then whichrow=(nj+1):totn;
			if j=pall then whichrow=1:((pall-1)#nj);
		
			yw=allw[whichrow, j]||allw[whichrow, whichcol];
			yw=yw-yw[:,]; 
			y=yw[, 1]; w=yw[, 2:(d+1)]; 

			Bhat=inv(w`*w)*w`*y; 

			meatmat=0; breadmat=0; 
			do i=1 to nall;  
			    score=w[i, ]`*(y[i]-w[i,]*Bhat);
				hess=-w[i,]`*w[i,];
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
	nj=oldnj;
	return(pvmat);  
finish;


/* Delete cycles based on p-values only */
start topsort(graphest, pvmat); 
	if (norm(graphest)=0) then goto emptygraph;

	NoNode=ncol(graphest);
	noid=(1:NoNode); topo=0;


	do while (ncol(topo)=1);
		anyrt=0;
		do j=1 to NoNode;
			if (norm(graphest[, j], "LInf")=0) then do;
				anyrt=anyrt+1;
				topo=topo||j; noid=noid[loc(noid^=j)]; 
			end;	
		end;
		
		if (anyrt=0) then do;
			/* set the "weakest" link at 0 */
			weakest=loc(pvmat=max(pvmat[loc(graphest^=0)]));
			graphest[weakest]=0;
			pvmat[weakest]=-1;
		end;
	end;
	
	topo=topo[2:ncol(topo)]`; remnd=nrow(noid); 
	if (remnd=1) then topo=topo||noid;
	temp=graphest;
	do while (remnd>1);
		temp=graphest[noid, noid]; 
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
			/* set the "weakest" link at 0 */
			weakest=loc(pvmat=max(pvmat[loc(graphest^=0)]));
			graphest[weakest]=0;
			pvmat[weakest]=-1;
		end;
		remnd=nrow(noid);
		if (remnd=1 & ncol(topo)<NoNode) then topo=topo||noid;
	end;

	emptygraph:
	return(graphest||topo`);
finish;

/* Delete cycles based on entries of regression coefficients in an initial regression coefficients matrix, return a DAG and a topological order */
start Khan(graphini); 
	NoNode=ncol(graphini);
	noid=(1:NoNode); topo=0;

	pvmat=abs(graphini); 

	do while (ncol(topo)=1);
		anyrt=0;
		do j=1 to NoNode;
			if (norm(graphini[, j], "LInf")=0) then do;
				anyrt=anyrt+1;
				topo=topo||j; noid=noid[loc(noid^=j)]; /* one problem here: loc(noid^=j) may not exist, noid is 1 by 1 */
			end;	
		end;
		
		if (anyrt=0) then do;
			/* set the "weakest" link at 0 */
			weakest=loc(pvmat=min(pvmat[loc(graphini^=0)]));
			graphini[weakest]=0;
			pvmat[weakest]=888;
		end;
	end;
	
	topo=topo[2:ncol(topo)]`; remnd=nrow(noid); 
	if (remnd=1) then topo=topo||noid;
	temp=graphini;
	do while (remnd>1);
		temp=graphini[noid, noid]; 
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
			/* set the "weakest" link at 0 */
			weakest=loc(pvmat=min(pvmat[loc(graphini^=0)]));
			graphini[weakest]=0;
			pvmat[weakest]=888;
		end;
		remnd=nrow(noid);
		if (remnd=1 & ncol(topo)<NoNode) then topo=topo||noid;
	end;

	
	return(graphini||topo`);
finish;



/* compute p-values used in PI score given two data set */
start meanvartest(sample1, sample2, samsize1, samsize2) global(varpvct); 
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

	if (pvar<varpvct) then do; /* two-sample t test without assuming equal variance */
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


/* Find PI scores and DISC scores of p nodes given two data sets from two networks and two estimated regression coefficients matrices */
start Find2score(PIscore, disc, tophowmany, allx1, allx2, bigBnow1, bigBnow2, randomseed) global(dall, NoNode, split, nj, NoObs, NoObsInt, pvcutoff); 
		/* Use the estimated graph structure to get unpenalized estimated regression coefficients */
		resids1to2=j(NoObs, NoNode, 0); resids2to1=j(NoObs, NoNode, 0); 
		resids1to1=j(NoObs, NoNode, 0); resids2to2=j(NoObs, NoNode, 0); 
		err12=j(NoObs, NoNode, 0); err21=j(NoObs, NoNode, 0); 
		do j=1 to NoNode;
			if (j>1 & j<NoNode) then whichrow=(1:((j-1)#nj))||((j#nj+1):NoObsInt); 
			if j=1 then whichrow=(nj+1):NoObsInt;
			if j=NoNode then whichrow=1:((NoNode-1)#nj);
			
			/* first assuming G1 structure */
			whichcol=loc(bigBnow1[, j]^=0); 

			d=ncol(whichcol);
			if (d>0) then do;
				yw=allx2[whichrow, j]||allx2[whichrow, whichcol];
				yw=yw-yw[:,]; 
				y=yw[, 1]; w=yw[, 2:(d+1)];
				trouble1=ginv(w`*w); trouble2=w`*y;
				resids1to2[, j]=y-w*trouble1*trouble2; /* Use X2 but B2-tilde (obtained by estimating B2 using X2 while assuming B1-hat structure) to find residuals */
				err21[, j]=y-w*bigBnow1[whichcol, j];  /* Use X2 data but B1-hat (obtainedestimating B1 using X1) to find residuals */

				yw=allx1[whichrow, j]||allx1[whichrow, whichcol];
				yw=yw-yw[:,]; 
				y=yw[, 1]; w=yw[, 2:(d+1)];
				resids1to1[, j]=y-w*bigBnow1[whichcol, j];
			end;
			else do; 
				y=allx2[whichrow, j];
				resids1to2[, j]=y-y[:];
				err21[, j]=y-y[:]; 

				y=allx1[whichrow, j];
				resids1to1[, j]=y-y[:];
			end;
		
			/* second assume G2 structure */
			whichcol=loc(bigBnow2[, j]^=0); 

			d=ncol(whichcol);
			if (d>0) then do;
				yw=allx1[whichrow, j]||allx1[whichrow, whichcol];
				yw=yw-yw[:,]; 
				y=yw[, 1]; w=yw[, 2:(d+1)];
				trouble1=ginv(w`*w); trouble2=w`*y;
				resids2to1[, j]=y-w*trouble1*trouble2;
				err12[, j]=y-w*bigBnow2[whichcol, j]; 

				yw=allx2[whichrow, j]||allx2[whichrow, whichcol];
				yw=yw-yw[:,]; 
				y=yw[, 1]; w=yw[, 2:(d+1)];
				resids2to2[, j]=y-w*bigBnow2[whichcol, j]; 
			end;
			else do; 
				y=allx1[whichrow, j];
				resids2to1[, j]=y-y[:];
				err12[, j]=y-y[:]; 

				y=allx2[whichrow, j];
				resids2to2[, j]=y-y[:];
			end;
		end;

		firsthalf=floor(dall/2); 
		samsize1=nj*firsthalf; samsize2=NoObs-samsize1;
		pvs1to2=j(NoNode, 3, 1); pvs2to1=j(NoNode, 3, 1); 
		pvs1to1=j(NoNode, 3, 1); pvs2to2=j(NoNode, 3, 1); 
		disc=j(NoNode, 1, 1);
		PIscore=0; tophowmany=0; 
		do sp=1 to split;
			mark=j(NoObs, 1, 2);
			call randseed(randomseed+sp);
			twoset=ranperm(dall);
			do expcond=1 to firsthalf;
				thiscond=twoset[expcond];
				mark[((thiscond-1)*nj+1):(thiscond*nj)]=1; 
			end;
			resids1=resids1to2[loc(mark=1), ];
			resids2=resids1to2[loc(mark=2), ];
			residsrv1=resids2to1[loc(mark=1), ];
			residsrv2=resids2to1[loc(mark=2), ];

			g1resids1=resids1to1[loc(mark=1), ]; 
			g1resids2=resids1to1[loc(mark=2), ]; 
			g2resids1=resids2to2[loc(mark=1), ]; 
			g2resids2=resids2to2[loc(mark=2), ]; 

			do j=1 to NoNode;
				/* Going from G1 to G2 */
				sample1=resids1[, j];
				sample2=resids2[, j];
				howcomp=meanvartest(sample1, sample2, samsize1, samsize2);
				pvs1to2[j, ]=howcomp;

				/* Going from G2 to G1 */
				sample1=residsrv1[, j];
				sample2=residsrv2[, j];
				howcomp=meanvartest(sample1, sample2, samsize1, samsize2);  
				pvs2to1[j, ]=howcomp;

				/* Going from G1 to G1 */
				sample1=g1resids1[, j];
				sample2=g1resids2[, j];
				howcomp=meanvartest(sample1, sample2, samsize1, samsize2);
				pvs1to1[j, ]=howcomp;

				/* Going from G2 to G2 */
				sample1=g2resids1[, j];
				sample2=g2resids2[, j];
				howcomp=meanvartest(sample1, sample2, samsize1, samsize2);
				pvs2to2[j, ]=howcomp;


				/* Computer DISCERN score */
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


/* Benjamini-Hochberg procedure: input original pvalues, output the node indices with significant p-values after BH adjustment */
start BHpv(pvs) global(fdr); 
	m=max(nrow(pvs),ncol(pvs)); 
	ids=do(1, m, 1)`;
	tag=ids||pvs;
	call sort(tag, 2);
	crt=fdr*(ids/m); /* this is the BH critical value for each sorted pvalue */
	lower=loc(tag[, 2]<crt);
	if ncol(lower)>0 then do;
		cutoff=lower[ncol(lower)];
		claim=tag[, 1][1:cutoff];
		return(claim); 
	end;
	else do;
		return(-1); /* this means no significant pvalues */
	end;
finish; 

/* Find driver nodes after identifying differential node */
start FindDriver(DiffNode, bigBnow1, bigBnow2) global(drivernodes, nodriv, notdriv);
	tophowmany=max(nrow(DiffNode), ncol(DiffNode)); 
	NoNode=ncol(bigBnow1); 
	driver=j(tophowmany, NoNode, 0);
	do k=1 to tophowmany;
		child=DiffNode[k]; 
		pa1=loc(bigBnow1[, child]^=0);
		pa2=loc(bigBnow2[, child]^=0);
		nopa1=ncol(pa1); nopa2=ncol(pa2); 

		if ((nopa1><nopa2)>0) then do;
			discrep=setdif(union(pa1, pa2), xsect(pa1, pa2)); /* the symmetric difference between two parent sets */
			if ncol(discrep)>0 then driver[k, discrep]=1;
		end;
		else do; 
			if (nopa1=0 & nopa2>0) then driver[k, pa2]=1; 
			if (nopa2=0 & nopa1>0) then driver[k, pa1]=1; 
		end;
	end;
	touched=loc(driver[+, ]>0);
	claimdriv=ncol(touched);
	if claimdriv>0 then do;
		pickdriv=sum(element(drivernodes, touched)); 
		tpr4driv=pickdriv/nodriv; 
		spe4driv=ncol(xsect(setdif(1:NoNode, touched), notdriv))/(NoNode-nodriv);  
		fdr4driv=ncol(xsect(touched, notdriv))/claimdriv; 
	end;
	else do;  /* do not claim any driver node */
		tpr4driv=0; spe4driv=1; fdr4driv=0; touched=j(1, NoNode, -88); 
	end;
	return(tpr4driv||spe4driv||fdr4driv||touched);
finish;

/*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*/
pall=30; rho1=0.3; rho2=0.3; bb=pall*rho1; cc=pall*rho2; aa=pall-bb-cc; 
nodiff=bb; wanttotal=4*pall;
ids=do(1, pall, 1)`; 
dall=pall-1; diagIdx = do(1, pall*pall, pall+1);	
sige=sqrt(0.25); 

sigx=1; 
optn=(pall-1)||0;
allpossible=pall*(pall-1)/2; 
allneg=allpossible-wanttotal;

pi=constant("pi"); twopi=2*pi; 
sndelta=0.9; snw=sige/sqrt(1-2*sndelta*sndelta/pi);
mnshift=snw*sqrt(2/pi)*sndelta;
NoNode=pall; 
dall=NoNode-1;

maxit=50; small=1e-3; small2=1e-4; small3=1e-6; threshold=1e-4; eps=1e-20; 
scada=3.7; 
varpvct=0.05; fdr=0.05;
pvcutoff=0.025;

lambmin=0.01; lambmax=0.5;
pvout=j(1, pall, .); 

rt=lambmin/lambmax;
m=20;
q=rt**(1/(m-1));

permno=10; /* Number of bootstrap samples */
njs={5, 10}; /* Number of intervention data points in each condition */ 
nonj=nrow(njs);

testout=j(1, 4+2*2*2*3, 0);
emppower=j(1, 1+2*2*8, 0); 

nographs=1;
MCrep=2; /* Number of Monte Carlo replicates */
jumpstart=4277;
split=10; case=2;
if case=1 then do; 
	maxparent=6; wanttotal=4#pall; 
end;
 
if case=2 then do;
	maxparent=20;
end;
takethisseed=0; 
do nog=1 to nographs;
	/* create two regression coefficients matrices */
	noedges=0; 
	edseed=takethisseed+1;
	blank=1; 

	/*~~~~~~~~~~~~~ Case 1: aa non-diff/non-driver nodes, bb diff nodes, and at most cc driver nodes ~~~~~~~~~~~~~*/
	if case=1 then do;
		do while (noedges^=wanttotal | blank=1);
			edseed=edseed+1; 
			call randseed(edseed);
			whatorder=ranperm(pall);
			bigBx=j(pall, pall, 0); 
			bigBx[, whatorder[1]]=0;
			nopar=j(pall, 1, 0);
			do k=2 to pall;
				thisnode=whatorder[k]; 
				nopar[k]=sample(0:min((k-1), maxparent), 1);
				if nopar[k]>0 then do;
					whichpar=sample(whatorder[1:k-1], nopar[k], "NoReplace"); 
					bigBx[whichpar, thisnode]=1;
				end; 
			end;
			noedges=ncol(loc(bigBx^=0)); 
			if noedges=wanttotal then do; 
				block3=bigBx[(aa+bb+1):pall, (aa+1):(aa+bb)];
				if (min(block3[+, ])>0) then blank=0; 
			end;
		end;
		takethisseed=edseed;
		
		/* Create another graph by deleting nonzero entries in certain blocks of bigBx  */
		bigBy=bigBx; 
		block3=bigBy[(aa+bb+1):pall, (aa+1):(aa+bb)];
		drivernodes=0;
		do k=1 to bb;
			candidates=loc(block3[, k]^=0); 
			call randseed(k+edseed);
			driver=sample(candidates, 1);
			block3[driver, k]=0;
			drivernodes=drivernodes||(driver+aa+bb);
		end;
		bigBy[(aa+bb+1):pall, (aa+1):(aa+bb)]=block3;
		noedgesy=sum(bigBy^=0);
		print noedges noedgesy;
		
		diffnodes=do(aa+1, aa+bb, 1); 
		drivernodes=unique(drivernodes[2:ncol(drivernodes)]);

		diffonly=diffnodes; 
		driveronly=drivernodes; 
		
		notdiff=setdif(ids, diffnodes); 
		notdriv=setdif(ids, drivernodes);
 
		nodriv=ncol(drivernodes);
		nodiff=ncol(diffnodes);
		print diffnodes drivernodes;	
	end;

	
	/*~~~~~~~~~~~~~~~ Case 2: at most bb diff nodes, at most cc driver nodes, allow overlapping ~~~~~~~~~~~~~~~~*/
	if case=2 then do;
		blank13=1;
		do while (blank13=1);
			edseed=edseed+1; 
			call randseed(edseed);
			whatorder=ranperm(pall);
			bigBx=j(pall, pall, 0); 
			bigBx[, whatorder[1]]=0;
			nopar=j(pall, 1, 0);
			do k=2 to pall;
				thisnode=whatorder[k]; 
				nopar[k]=sample(0:min((k-1), maxparent), 1);
				if nopar[k]>0 then do;
					whichpar=sample(whatorder[1:k-1], nopar[k], "NoReplace"); 
					bigBx[whichpar, thisnode]=1;
				end; 
			end;
			noedges=ncol(loc(bigBx^=0));

			block13=bigBx[(aa+1):pall, (aa+1):(aa+bb)];
			if (min(block13[+, ])>0) then blank13=0;
		end;
		takethisseed=edseed;
		wanttotal1=noedges; 

		/* Create another graph by deleting nonzero entries in certain blocks of bigBx  */
		bigBy=bigBx; 
		block3=bigBy[(aa+bb+1):pall, (aa+1):(aa+bb)];
		block1=bigBy[(aa+1):(aa+bb), (aa+1):(aa+bb)];
		drivernodes=0; diffnodes=0;
		do k=1 to bb;
			candidates=loc(block3[, k]^=0);
			if ncol(candidates)>0 then do;
				call randseed(k);
				driver=sample(candidates, 1);
				block3[driver, k]=0;
				diffnodes=diffnodes||(k+aa);
				drivernodes=drivernodes||(driver+aa+bb);
			end; 

			candidates=loc(block1[, k]^=0); 
			if ncol(candidates)>0 then do;
				call randseed(k+9000);
				driver=sample(candidates, 1);
				block1[driver, k]=0;
				diffnodes=diffnodes||(k+aa);
				drivernodes=drivernodes||(driver+aa);
			end;
		end;
		bigBy[(aa+bb+1):pall, (aa+1):(aa+bb)]=block3;
		bigBy[(aa+1):(aa+bb), (aa+1):(aa+bb)]=block1;
		noedges2=ncol(loc(bigBy^=0));
		wanttotal2=noedges2;

		print noedges noedges2;
		diffnodes=unique(diffnodes[2:ncol(diffnodes)]);
		drivernodes=unique(drivernodes[2:ncol(drivernodes)]);
		bothnodes=xsect(diffnodes, drivernodes);
		driveronly=setdif(drivernodes, bothnodes);

		diffonly=setdif(diffnodes, bothnodes); 
		notdiff=setdif(ids, diffnodes); 
		notdriv=setdif(ids, drivernodes);
		
		nodriv=ncol(drivernodes);
		nodiff=ncol(diffnodes); 
		noboth=ncol(bothnodes);
		print diffnodes drivernodes bothnodes;
	end;
	neitherrole=setdif(setdif(1:pall, diffnodes), drivernodes); 

	u=j(pall*pall, 1, 1);
	call randseed(nog+77777);
	call randgen(u, "Uniform"); 
	
	fillin=loc(bigBx^=0);
	call randseed(nog+333321); 
	bf = rand("Bernoulli", repeat(0.5, ncol(fillin)));
	bigBx[fillin]=u[1:ncol(fillin)]+bf-(1-bf)*2;

	call randseed(nog+765);
	call randgen(u, "Uniform"); 
	
	fillin=loc(bigBy^=0);
	call randseed(nog+321); 
	bf = rand("Bernoulli", repeat(0.5, ncol(fillin)));
	bigBy[fillin]=u[1:ncol(fillin)]+bf-(1-bf)*2;

	revisey=Khan(bigBy);
	bigBy=revisey[, 1:pall]; 
	whatordery=revisey[, pall+1]`;
	nopary=j(pall, 1, 0);
	do k=2 to pall; 
		thischild=whatordery[k];
		itsparent=loc(bigBy[, thischild]^=0);
		if ncol(itsparent)>0 then nopary[k]=ncol(itsparent);
	end; 

	
	do whichnj=1 to nonj; 
		nj=njs[whichnj]; totn=pall*nj;  
		NoObsInt=totn; NoObs=totn-nj;
		bicpen1=log(NoObs)/NoObs; 
		NoObsInt2=NoObsInt; NoObs2=totn-nj;
		bicpen2=log(NoObs2)/NoObs2;
		
		do rep=1 to MCrep;  
			duetoemp:
		   	seedx=j(NoObs, 1, 341+nog+rep+whichnj+jumpstart); 
			seedxj=j(nj, 1, 451+nog+rep+whichnj+jumpstart);
			seede=j(NoObs, 1, 4351+nog+rep+whichnj+jumpstart); 
			seedu=j(NoObsInt, pall, 321+nog+rep+whichnj+jumpstart);	
			
			allx1=j(totn, pall, 0); allx2=allx1; 
			call randseed(399999+nog+rep+whichnj+jumpstart);
			u = j(2*nj, 1);                
			call randgen(u, "Uniform"); 
			
			root=whatorder[1]; 
			if (root>1 & root<pall) then whichrow=(1:((root-1)#nj))||((root#nj+1):totn);
			if root=1 then whichrow=(nj+1):totn;
			if root=pall then whichrow=1:((pall-1)#nj);
			allx1[((root-1)*nj+1):(root*nj), whatorder[1]]=u[1:nj]; /* interventional data for the root node */
			allx1[whichrow, whatorder[1]]=sige#normal(seedx);    /* not interventional data but data according to the regression model for a root node */

			root=whatordery[1]; 
			if (root>1 & root<pall) then whichrow=(1:((root-1)#nj))||((root#nj+1):totn);
			if root=1 then whichrow=(nj+1):totn;
			if root=pall then whichrow=1:((pall-1)#nj);
			allx2[((root-1)*nj+1):(root*nj), whatordery[1]]=u[(nj+1):(2*nj)]; /* interventional data for the root node */
			allx2[whichrow, whatordery[1]]=sige#normal(seedx+9754); /* not interventional data but data according to the regression model for a root node */
			do k=2 to pall;
				thisnode=whatorder[k]; 
				call randseed(123+nog+rep+whichnj+k);
				u = j(2*nj, 1);
				call randgen(u, "Uniform"); 
				if (thisnode>1 & thisnode<pall) then whichrow=(1:((thisnode-1)#nj))||((thisnode#nj+1):totn);
				if thisnode=1 then whichrow=(nj+1):totn;
				if thisnode=pall then whichrow=1:((pall-1)#nj);
					
				allx1[((thisnode-1)#nj+1):(thisnode#nj), thisnode]=u[1:nj];
				if nopar[k]>0 then do;
					whichpar=loc(bigBx[, thisnode]^=0);
					/* generate Gaussian DAG */
					allx1[whichrow, thisnode]=allx1[whichrow, whichpar]*bigBx[whichpar, thisnode]+sige#normal(seede+k);
					modelerr1=normal(seede+k); modelerr2=normal(seede+k+99999);
					modelerr=sndelta#modelerr1+sqrt(1-sndelta#sndelta)#modelerr2;
					modelerr=modelerr#(modelerr1>=0)-modelerr#(modelerr1<0);
					modelerr=snw*modelerr-mnshift;
					allx1[whichrow, thisnode]=sqrt(abs(allx1[whichrow, whichpar]))*bigBx[whichpar, thisnode]+modelerr;
				end; 
				else allx1[whichrow, thisnode]=sige#normal(seedx+k);
				
				thisnode=whatordery[k]; 
				if (thisnode>1 & thisnode<pall) then whichrow=(1:((thisnode-1)#nj))||((thisnode#nj+1):totn);
				if thisnode=1 then whichrow=(nj+1):totn;
				if thisnode=pall then whichrow=1:((pall-1)#nj);
					
				allx2[((thisnode-1)#nj+1):(thisnode#nj), thisnode]=u[(nj+1):(2*nj)];
				if nopary[k]>0 then do;
					whichpar=loc(bigBy[, thisnode]^=0);
					/* generate Gaussian DAG */
					allx2[whichrow, thisnode]=allx2[whichrow, whichpar]*bigBy[whichpar, thisnode]+sige#normal(seede+k+8766655);
				end; 
				else allx2[whichrow, thisnode]=sige#normal(seedx+k+9898765);
			end;

			NoObs=totn-nj;
	
			/*---------------- Done with graph and data generation. ----------------*/
			bigBnow1=j(pall, pall, 0);
			/**~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Estimate B1 & B2 ~~~~~~~~~~~~~~~~~~~~~~~~~~**/
			/* Get the non-penalized ls score estimates as starting values of bigB. */
			bigBini1=j(NoNode, NoNode, 0); bigBini2=j(NoNode, NoNode, 0); 
			do j=1 to NoNode; 
				ignorej=loc((1:NoNode)^=j);
				if (j>1 & j<NoNode) then whichrow=(1:((j-1)#nj))||((j#nj+1):NoObsInt);
				if j=1 then whichrow=(nj+1):NoObsInt;
				if j=NoNode then whichrow=1:((NoNode-1)#nj);

				w=allx1[whichrow, ignorej];
				y=allx1[whichrow, j];
				y=y-y[:]; w=w-w[:, ]; 
				bigBini1[ignorej, j]=inv(w`*w)*w`*y;

				w=allx2[whichrow, ignorej];
				y=allx2[whichrow, j];
				y=y-y[:]; w=w-w[:, ]; 
				bigBini2[ignorej, j]=inv(w`*w)*w`*y;
			end;
			
			/* make the initial B not contain [i,j] and [j,i] entries both nonzero */
			do i=1 to (NoNode-1); 
				do j=i+1 to NoNode;
					if abs(bigBini1[i,j])<=abs(bigBini1[j,i]) then bigBini1[i,j]=0;
					else bigBini1[j,i]=0;

					if abs(bigBini2[i,j])<=abs(bigBini2[j,i]) then bigBini2[i,j]=0;
					else bigBini2[j,i]=0;
				end;
			end;

			run Tuning(lambda1, lambda2, bigBnow1, bigBnow2, lambmax, m, q, allx1, allx2, bigBini1, bigBini2);
			randomseed=34646+nog+rep+whichnj;
			run Find2score(PIscore, disc, tophowmany, allx1, allx2, bigBnow1, bigBnow2, randomseed); 
	
			if (norm(bigBnow1)=0 | norm(bigBnow2)=0) then do;
				jumpstart=jumpstart+77777;
				goto duetoemp;
			end;

			/* Claim the top "tophowmany" nodes as differential nodes based on the score ranking */	
			role_PI=j(NoNode, 2, 0); role_disc=j(NoNode, 2, 0); /* record for each node: "1" in 1st column if differential node, in the 2nd column if driver */
			if tophowmany>0 then do;
				keeptrack=ids||PIscore;
				call sort(keeptrack, 2, 2); 
				diffnd=keeptrack[1:tophowmany, 1];
				if ncol(diffnd)>0 then do;
					role_PI[diffnd, 1]=1; 
					pickdiff=sum(element(diffnodes, diffnd));  /* the number of differential nodes that are also the top tophowmany nodes according to PI score */
					tpr4diff=pickdiff/nodiff; 
					spe4diff=ncol(xsect(setdif(ids, diffnd), notdiff))/(pall-nodiff); 
					fdr4diff=ncol(xsect(diffnd, notdiff))/max(ncol(diffnd), nrow(diffnd));
					PIdiff_rnk=tpr4diff||spe4diff||fdr4diff; 
					allout=FindDriver(diffnd, bigBnow1, bigBnow2);
					PIdriv_rnk=allout[1:3]`; /* record tpr, spe, and fdr for driver nodes identification */
					role_PI[allout[4:ncol(allout)], 2]=1; 
				end;
				else do;
					PIdiff_rnk=0||1||0; PIdriv_rnk=0||1||0;
				end;

				keeptrack=do(1, pall, 1)`||disc;
				call sort(keeptrack, 2, 2); 
				diffnd=keeptrack[1:tophowmany, 1];
				if ncol(diffnd)>0 then do;
					role_disc[diffnd, 1]=1; 
					pickdiff=sum(element(diffnodes, diffnd));  /* the number of differential nodes that are also the top tophowmany nodes according to DISC score */
					tpr4diff=pickdiff/nodiff; 							
					spe4diff=ncol(xsect(setdif(ids, diffnd), notdiff))/(NoNode-nodiff); 
					fdr4diff=ncol(xsect(diffnd, notdiff))/max(ncol(diffnd), nrow(diffnd)); 
					discdiff_rnk=tpr4diff||spe4diff||fdr4diff;
					allout=FindDriver(diffnd, bigBnow1, bigBnow2);
					discdriv_rnk=allout[1:3]`;
					role_disc[allout[4:ncol(allout)], 2]=1;
				end;
				else do;
					discdiff_rnk=0||1||0; discdriv_rnk=0||1||0;
				end;
			end;
			else do; 
				PIdiff_rnk=0||1||0; PIdriv_rnk=0||1||0;
				discdiff_rnk=0||1||0; discdriv_rnk=0||1||0;
			end;	

		
			/* Use re-sampled data to identify differential nodes and driver nodes (to get some power assessment) */	
			freq_PI=j(NoNode, 2, 0); freq_disc=j(NoNode, 2, 0); 
			do perm=1 to permno; 
				call randseed(7746+nog+rep+whichnj+perm);
				unitidx=sample(1:nj);
				allpermx1=allx1[unitidx, ]; 
				allpermx2=allx2[unitidx, ];
				
				
				do expcond=2 to pall;
					 call randseed(576848+nog+rep+whichnj+perm+expcond);
     				 unitidx=ranperm(((expcond-1)*nj+1):(expcond*nj));
					 allpermx1=allpermx1//allx1[unitidx, ]; 
					 allpermx2=allpermx2//allx2[unitidx, ];
				end; 			

				bigBnow1_perm=findgraph2(lambda1, allpermx1, bigBnow1); 
				if (norm(bigBnow1_perm)=0) then do;
					jumpstart=jumpstart+77777;
					goto duetoemp;
				end;

				pvmat=getpv2(bigBnow1_perm, allpermx1);
				bigBnow1_perm=topsort(bigBnow1_perm, pvmat)[, 1:NoNode];
				
				bigBnow2_perm=findgraph2(lambda2, allpermx2, bigBnow2); 
				if (norm(bigBnow2_perm)=0) then do;
					jumpstart=jumpstart+77777;
					goto duetoemp;
				end;

				pvmat=getpv2(bigBnow2_perm, allpermx2);
				bigBnow2_perm=topsort(bigBnow2_perm, pvmat)[, 1:NoNode];

				randomseed=88886+nog+rep+whichnj+perm;
				run Find2score(PIscore_perm, disc_perm, tophowmany_perm, allpermx1, allpermx2, bigBnow1_perm, bigBnow2_perm, randomseed); 			

				if tophowmany_perm>0 then do;
					keeptrack=do(1, NoNode, 1)`||PIscore_perm;
					call sort(keeptrack, 2, 2); 
					diffnd=keeptrack[1:tophowmany_perm, 1];
					if ncol(diffnd)>0 then do;
						freq_PI[diffnd, 1]=freq_PI[diffnd, 1]+1; 
						allout=FindDriver(diffnd, bigBnow1_perm, bigBnow2_perm);
						freq_PI[allout[4:ncol(allout)], 2]=freq_PI[allout[4:ncol(allout)], 2]+1; 
					end;

					keeptrack=do(1, NoNode, 1)`||disc_perm;
					call sort(keeptrack, 2, 2); 
					diffnd=keeptrack[1:tophowmany_perm, 1];
					if ncol(diffnd)>0 then do;
						freq_disc[diffnd, 1]=freq_disc[diffnd, 1]+1; 
						allout=FindDriver(diffnd, bigBnow1_perm, bigBnow2_perm);
						freq_disc[allout[4:ncol(allout)], 2]=freq_disc[allout[4:ncol(allout)], 2]+1;
					end;
				end;
			end;
			freq_PI=freq_PI/permno; freq_disc=freq_disc/permno;  

			
			if ncol(bothnodes)>0 then do; 
				/* The following are the empirical power (mean, median) according to PI/disc scores for differential node identification */
				diffpower=mean(freq_PI[diffonly, 1])||median(freq_PI[diffonly, 1])||mean(freq_PI[driveronly, 1])||median(freq_PI[driveronly, 1])	
						||mean(freq_PI[bothnodes, 1])||median(freq_PI[bothnodes, 1])||mean(freq_PI[neitherrole, 1])||median(freq_PI[neitherrole, 1])
						||mean(freq_disc[diffonly, 1])||median(freq_disc[diffonly, 1])||mean(freq_disc[driveronly, 1])||median(freq_disc[driveronly, 1])
						||mean(freq_disc[bothnodes, 1])||median(freq_disc[bothnodes, 1])||mean(freq_disc[neitherrole, 1])||median(freq_disc[neitherrole, 1]);

				/* The following are the empirical power (mean, median) according to PI/disc scores for driver node identification */
				drivpower=mean(freq_PI[diffonly, 2])||median(freq_PI[diffonly, 2])||mean(freq_PI[driveronly, 2])||median(freq_PI[driveronly, 2])
						||mean(freq_PI[bothnodes, 2])||median(freq_PI[bothnodes, 2])||mean(freq_PI[neitherrole, 2])||median(freq_PI[neitherrole, 2])
						||mean(freq_disc[diffonly, 2])||median(freq_disc[diffonly, 2])||mean(freq_disc[driveronly, 2])||median(freq_disc[driveronly, 2])
						||mean(freq_disc[bothnodes, 2])||median(freq_disc[bothnodes, 2])||mean(freq_disc[neitherrole, 2])||median(freq_disc[neitherrole, 2]);
			end; 
			else do; 
				/* The following are the empirical power (mean, median) according to PI/disc scores for differential node identification */
				diffpower=mean(freq_PI[diffonly, 1])||median(freq_PI[diffonly, 1])||mean(freq_PI[driveronly, 1])||median(freq_PI[driveronly, 1])	
						||0||0||mean(freq_PI[neitherrole, 1])||median(freq_PI[neitherrole, 1])
						||mean(freq_disc[diffonly, 1])||median(freq_disc[diffonly, 1])||mean(freq_disc[driveronly, 1])||median(freq_disc[driveronly, 1])
						||0||0||mean(freq_disc[neitherrole, 1])||median(freq_disc[neitherrole, 1]);

				/* The following are the empirical power (mean, median) according to PI/disc scores for driver node identification */
				drivpower=mean(freq_PI[diffonly, 2])||median(freq_PI[diffonly, 2])||mean(freq_PI[driveronly, 2])||median(freq_PI[driveronly, 2])
						||0||0||mean(freq_PI[neitherrole, 2])||median(freq_PI[neitherrole, 2])
						||mean(freq_disc[diffonly, 2])||median(freq_disc[diffonly, 2])||mean(freq_disc[driveronly, 2])||median(freq_disc[driveronly, 2])
						||0||0||mean(freq_disc[neitherrole, 2])||median(freq_disc[neitherrole, 2]);
			end;

			
			/* Identify differential nodes and driver nodes based on the empirical power */	
			diffnd=loc(freq_PI[, 1]>0.5); 
			if ncol(diffnd)>0 then do;
				pickdiff=sum(element(diffnodes, diffnd));  /* the number of differential nodes that are also the top tophowmany nodes according to PI score */
				tpr4diff=pickdiff/nodiff; 
				spe4diff=ncol(xsect(setdif(ids, diffnd), notdiff))/(pall-nodiff); 
				fdr4diff=ncol(xsect(diffnd, notdiff))/max(ncol(diffnd), nrow(diffnd));
				PIdiff_emppw=tpr4diff||spe4diff||fdr4diff; 
			end;
			else PIdiff_emppw=0||1||0; 
			drivnd=loc(freq_PI[, 2]>0.5); 
			if ncol(drivnd)>0 then do; 
				pickdriv=sum(element(drivernodes, drivnd));  /* the number of driver nodes that are identified by empirical power of PI score */
				tpr4driv=pickdriv/nodriv; 
				spe4driv=ncol(xsect(setdif(ids, drivnd), notdriv))/(pall-nodriv); 
				fdr4driv=ncol(xsect(drivnd, notdriv))/max(ncol(drivnd), nrow(drivnd));
				PIdriv_emppw=tpr4driv||spe4driv||fdr4driv; 
			end;
			else PIdriv_emppw=0||1||0;

			diffnd=loc(freq_disc[, 1]>0.5);
			if ncol(diffnd)>0 then do;
				pickdiff=sum(element(diffnodes, diffnd));  /* the number of differential nodes that are also the top tophowmany nodes according to DISC score */
				tpr4diff=pickdiff/nodiff; 							
				spe4diff=ncol(xsect(setdif(ids, diffnd), notdiff))/(NoNode-nodiff); 
				fdr4diff=ncol(xsect(diffnd, notdiff))/max(ncol(diffnd), nrow(diffnd)); 
				discdiff_emppw=tpr4diff||spe4diff||fdr4diff;
			end;
			else discdiff_emppw=0||1||0; 
			drivnd=loc(freq_disc[, 2]>0.5);
			if ncol(drivnd)>0 then do; 
				pickdriv=sum(element(drivernodes, drivnd));  /* the number of driver nodes that are identified by empirical power of PI score */
				tpr4driv=pickdriv/nodriv; 
				spe4driv=ncol(xsect(setdif(ids, drivnd), notdriv))/(pall-nodriv); 
				fdr4driv=ncol(xsect(drivnd, notdriv))/max(ncol(drivnd), nrow(drivnd));
				discdriv_emppw=tpr4driv||spe4driv||fdr4driv; 
			end;
			else discdriv_emppw=0||1||0;
			
			emppower=emppower//(nj||diffpower||drivpower);
			testout=testout//(nj||lambda1||lambda2||tophowmany||PIdiff_rnk||discdiff_rnk||PIdiff_emppw||discdiff_emppw||PIdriv_rnk||discdriv_rnk||PIdriv_emppw||discdriv_emppw);			
		end;
		
	end;
end;
testout=testout[2:nrow(testout), ];
emppower=emppower[2:nrow(emppower), ];

create out.power888 from testout[colname=('nj'||'lambda1'||'lambda2'||'tophowmany'
||'PItpr4diff_rnk'||'PIspe4diff_rnk'||'PIfdr4diff_rnk'||'DISCtpr4diff_rnk'||'DISCspe4diff_rnk'||'DISCfdr4diff_rnk'
||'PItpr4diff_emppw'||'PIspe4diff_emppw'||'PIfdr4diff_emppw'||'DISCtpr4diff_emppw'||'DISCspe4diff_emppw'||'DISCfdr4diff_emppw'
||'PItpr4driv_rnk'||'PIspe4driv_rnk'||'PIfdr4driv_rnk'||'DISCtpr4driv_rnk'||'DISCspe4driv_rnk'||'DISCfdr4driv_rnk'
||'PItpr4driv_emppw'||'PIspe4driv_emppw'||'PIfdr4driv_emppw'||'DISCtpr4driv_emppw'||'DISCspe4driv_emppw'||'DISCfdr4driv_emppw')]; 
append from testout; 

create out.emppower888 from emppower[colname=
		('nj'||'DfOmn_PIdiff'||'DfOmd_PIdiff'||'DrOmn_PIdiff'||'DrOmd_PIdiff'||'DfDrmn_PIdiff'||'DfDrmd_PIdiff'||'Neitmn_PIdiff'||'Neitmd_PIdiff'
	   		 ||'DfOmn_DISCdiff'||'DfOmd_DISCdiff'||'DrOmn_DISCdiff'||'DrOmd_DISCdiff'||'DfDrmn_DISCdiff'||'DfDrmd_DISCdiff'||'Neitmn_DISCdiff'||'Neitmd_DISCdiff'
			 ||'DfOmn_PIdriv'||'DfOmd_PIdriv'||'DrOmn_PIdriv'||'DrOmd_PIdriv'||'DfDrmn_PIdriv'||'DfDrmd_PIdriv'||'Neitmn_PIdriv'||'Neitmd_PIdriv'
	   		 ||'DfOmn_DISCdriv'||'DfOmd_DISCdriv'||'DrOmn_DISCdriv'||'DrOmd_DISCdriv'||'DfDrmn_DISCdriv'||'DfDrmd_DISCdriv'||'Neitmn_DISCdriv'||'Neitmd_DISCdriv')]; 
append from emppower;
quit; 
proc sort data=out.power888; by nj;
run; 

proc means data=out.power888 mean stderr median n;
	by nj;
run;

proc sort data=out.emppower888; by nj;
run; 

proc means data=out.emppower888 mean stderr median n;
	by nj;
run;

data track;
    t=time(); d=today();
    put 'Time: ' t time9.;
    put 'Date: ' d date9.;
run;

quit;

