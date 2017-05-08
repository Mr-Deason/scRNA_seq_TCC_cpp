#include <iostream>
#include <stdio.h>
#include <string.h>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <time.h>
#include <omp.h>
#include <boost\filesystem.hpp>
#include <zlib.h>
#include "kseq.h"

using namespace std;
namespace fs = boost::filesystem;

KSEQ_INIT(gzFile, gzread);

unsigned int code_map(char ch)
{
	if (ch == 'A') return 0;
	if (ch == 'G') return 1;
	if (ch == 'C') return 2;
	if (ch == 'T') return 3;
	if (ch == 'N') return 0*(rand()%3);
}
unsigned int encode(string str)
{
	unsigned int code = 0;
	for (int i = 0; str[i]; ++i)
	{
		code <<= 2;
		code |= code_map(str[i]);
	}
	return code;
}

char* str_AGCT = "AGCT";
string decode(unsigned int code, int len)
{
	string ret;
	ret.resize(len);
	for (int i = 0; i < len; ++i)
	{
		ret[len - i - 1] = str_AGCT[code & 3];
		code >>= 2;
	}
	return ret;
}


#define  MMAX  6

typedef  float MAT[MMAX + 2][MMAX + 2];

void LUBKSB(MAT A, int N, int np, int *INDX, float *B) {

	float SUM;
	int I, II, J, LL;

	II = 0;

	for (I = 1; I <= N; I++) {
		LL = INDX[I];
		SUM = B[LL];
		B[LL] = B[I];
		if (II != 0)
			for (J = II; J<I; J++)
				SUM -= A[I][J] * B[J];
		else if (SUM != 0.0)
			II = I;
		B[I] = SUM;
	}

	for (I = N; I>0; I--) {
		SUM = B[I];
		if (I < N)
			for (J = I + 1; J <= N; J++)
				SUM -= A[I][J] * B[J];
		B[I] = SUM / A[I][I];
	}

}
void LUDCMP(MAT A, int N, int np, int *INDX, int *D, int *CODE) {

	float AMAX, DUM, SUM, TINY;
	float VV[1000];
	int   I, IMAX, J, K;

	TINY = (float)1e-12;

	*D = 1; *CODE = 0;

	for (I = 1; I <= N; I++) {
		AMAX = 0.0;
		for (J = 1; J <= N; J++)
			if (fabs(A[I][J]) > AMAX) AMAX = (float)fabs(A[I][J]);
		if (AMAX < TINY) {
			*CODE = 1;
			return;
		}
		VV[I] = (float)1.0 / AMAX;
	}

	for (J = 1; J <= N; J++) {
		for (I = 1; I<J; I++) {
			SUM = A[I][J];
			for (K = 1; K<I; K++)
				SUM -= A[I][K] * A[K][J];
			A[I][J] = SUM;
		}
		AMAX = 0.0;
		for (I = J; I <= N; I++) {
			SUM = A[I][J];
			for (K = 1; K<J; K++)
				SUM -= A[I][K] * A[K][J];
			A[I][J] = SUM;
			DUM = VV[I] * (float)fabs(SUM);
			if (DUM >= AMAX) {
				IMAX = I;
				AMAX = DUM;
			}
		}

		if (J != IMAX) {
			for (K = 1; K <= N; K++) {
				DUM = A[IMAX][K];
				A[IMAX][K] = A[J][K];
				A[J][K] = DUM;
			}
			*D = -(*D);
			VV[IMAX] = VV[J];
		}

		INDX[J] = IMAX;
		if ((float)fabs(A[J][J]) < TINY)  A[J][J] = TINY;

		if (J != N) {
			DUM = (float)1.0 / A[J][J];
			for (I = J + 1; I <= N; I++)  A[I][J] *= DUM;
		}
	} //j loop

} //LUDCMP()


void savgol_coeff(float *c, int np, int nl, int nr, int ld, int m) {
	/*-------------------------------------------------------------------------------------------
	USES lubksb,ludcmp given below.
	Returns in c(np), in wrap-around order (see reference) consistent with the argument respns
	in routine convlv, a set of Savitzky-Golay filter coefficients. nl is the number of leftward
	(past) data points used, while nr is the number of rightward (future) data points, making
	the total number of data points used nl +nr+1. ld is the order of the derivative desired
	(e.g., ld = 0 for smoothed function). m is the order of the smoothing polynomial, also
	equal to the highest conserved moment; usual values are m = 2 or m = 4.
	-------------------------------------------------------------------------------------------*/
	int d, icode, imj, ipj, i, j, k, kk, mm;
	int indx[MMAX + 2];
	float fac, sum;
	MAT   a;
	float b[MMAX + 2];

	if (np<nl + nr + 1 || nl<0 || nr<0 || ld>m || m>MMAX || nl + nr<m) {
		printf("\n Bad args in savgol.\n");
		return;
	}

	for (i = 1; i <= MMAX + 1; i++) {
		for (j = 1; j <= MMAX + 1; j++) a[i][j] = 0.0;
		b[i] = 0.0;
		indx[i] = 0;
	}

	for (ipj = 0; ipj <= 2 * m; ipj++) { //Set up the normal equations of the desired leastsquares fit.
		sum = 0.0;
		if (ipj == 0) sum = 1.0;
		for (k = 1; k <= nr; k++) sum += (float)pow(k, ipj);
		for (k = 1; k <= nl; k++) sum += (float)pow(-k, ipj);
		mm = ipj <=  2 * m - ipj ? ipj : 2 * m - ipj;
		imj = -mm;
		do {
			a[1 + (ipj + imj) / 2][1 + (ipj - imj) / 2] = sum;
			imj += 2;
		} while (imj <= mm);
	}

	LUDCMP(a, m + 1, MMAX + 1, indx, &d, &icode);    //Solve them: LU decomposition

	for (j = 1; j <= m + 1; j++) b[j] = 0.0;
	b[ld + 1] = 1.0;    //Right-hand side vector is unit vector, depending on which derivative we want.

	LUBKSB(a, m + 1, MMAX + 1, indx, b);      //Backsubstitute, giving one row of the inverse matrix.

	for (kk = 1; kk <= np; kk++)          //Zero the output array (it may be bigger than the number
		c[kk] = 0.0;                      //of coefficients.

	for (k = -nl; k <= nr; k++) {         //Each Savitzky-Golay coefficient is the dot product
		sum = b[1];                       //of powers of an integer with the inverse matrix row.
		fac = 1.0;
		for (mm = 1; mm <= m; mm++) {
			fac *= k;
			sum += b[mm + 1] * fac;
		}
		kk = ((np - k) % np) + 1;           //Store in wrap-around order}
		c[kk] = sum;
	}
}

float* savgol_filter(float *data, int n, int win_len, int polyorder)
{
	float* ret = (float*)malloc((n+2) * sizeof(float));
	memset(ret, 0, (n + 2) *sizeof(float));
	int nl = win_len / 2;
	int nr = win_len / 2;
	int m = polyorder;

	int *index = (int*)malloc((win_len + 2) * sizeof(int));
	memset(index, 0, (win_len + 2) * sizeof(int));
	index[1] = 0;
	int j = 3;
	for (int i = 2; i <= nl + 1; i++) {
		index[i] = i - j;
		j += 2;
	}
	j = 2;
	for (int i = nl + 2; i <= nl + nr + 1; i++) {
		index[i] = i - j;
		j += 2;
	}

	float *c = (float*)malloc((win_len + 2) * sizeof(float));
	memset(c, 0, (win_len + 2) * sizeof(float));
	savgol_coeff(c, nl + nr + 1, nl, nr, 0, m);

	for (int i = 1; i <= n - nr; i++) {
		ret[i] = 0.0;
		for (j = 1; j <= nl + nr + 1; j++)
			if (i + index[j]>0)   //skip left points that do not exist.
				ret[i] += c[j] * data[i + index[j]-1];
	}

	free(index);
	free(c);
	return ret+1;
}

int main(int argc, char *argv[])
{
	fs::create_directory("./out");
	vector<string> files;
	srand(clock());

	static int BARCODE_LENGTH = 14;
	static int D_MIN = 5;

	fs::path fastq_dir("../example_dataset/fastq_files/");
	if (exists(fastq_dir) && fs::is_directory(fastq_dir))
	{
		for (fs::directory_entry ite : fs::directory_iterator(fastq_dir))
			if (fs::is_regular_file(ite))
				files.push_back(ite.path().string());
		sort(files.begin(), files.end());
	}

	vector<unsigned int> barcodes;
	for (int i = 0; i < files.size()/2; ++i)
	{
		cout << files[i] << endl;
		gzFile fp = gzopen(files[i].c_str(), "r");
		kseq_t *seq1;
		seq1 = kseq_init(fp);
		int l;
		while ((l = kseq_read(seq1) >= 0))
		{
			string bar = seq1->seq.s;
			//printf("%s\n", bar.c_str());
			barcodes.push_back(encode(bar));
		}
		gzclose(fp);
		kseq_destroy(seq1);
	}
	cout << barcodes.size() << endl;

	map<unsigned int, int> barcodes_cnt;
	for (int i = 0; i < barcodes.size(); ++i)
	{
		barcodes_cnt[barcodes[i]]--;
	}
	cout << barcodes_cnt.size() << endl;

	vector<pair<int, unsigned int> > cnt_bar;
	for (map<unsigned int, int>::iterator ite = barcodes_cnt.begin(); ite != barcodes_cnt.end(); ++ite)
	{
		cnt_bar.push_back(make_pair(ite->second, ite->first));
	}

	sort(cnt_bar.begin(), cnt_bar.end());
	for (int i = 0; i < 10 && i < cnt_bar.size(); ++i)
		cout << cnt_bar[i].first << ' ' << decode(cnt_bar[i].second, BARCODE_LENGTH) << endl;


	float *diff = (float*)malloc(cnt_bar.size() * sizeof(float));
	for (int i = 0; i < cnt_bar.size()-1; ++i)
	{
		diff[i] = cnt_bar[i].first - cnt_bar[i + 1].first;
	}
	int WINDOWS[2] = { 500, 5000 };
	float *yhat = savgol_filter(diff, cnt_bar.size() - 1, 151, 1);

	for (int i = 0; i < 100; ++i)
	{
		cout << yhat[i] << ' ';
	}

	int border = WINDOWS[0];
	for (int i = WINDOWS[0]; i < WINDOWS[1]; ++i)
		if (yhat[border] > yhat[i])
			border = i;
	
	int num_barcodes = border;
	int num_reads = 0;
	int *codewords = new int[num_barcodes];
	for (int i = 0; i < num_barcodes; ++i)
	{
		num_reads -= cnt_bar[i].first;
		codewords[i] = cnt_bar[i].second;
	}
	cout << endl;
	cout << "Cell_barcodes_detected: " << num_barcodes << endl;
	cout << "NUM_OF_READS_in_CELL_BARCODES = " << num_reads << endl;

	///to delete
	sort(codewords, codewords + num_barcodes);
	FILE *fp = fopen("codewords.txt", "w");
	for (int i = 0; i < num_barcodes; ++i)
	{
		fprintf(fp, "%s\n", decode(codewords[i], BARCODE_LENGTH).c_str());
	}
	fclose(fp);

	int **dist = new int*[num_barcodes];
	for (int i = 0; i < num_barcodes; ++i)
		dist[i] = new int[num_barcodes];

	for (int i = 0; i < num_barcodes; ++i)
	{
		dist[i][i] = BARCODE_LENGTH + 1;
		for (int j = i + 1; j < num_barcodes; ++j)
		{
			dist[i][j] = 0;
			unsigned int d = codewords[i] ^ codewords[j];
			for (int k = 0; k < BARCODE_LENGTH; ++k)
			{
				if (d & 3)
					++dist[i][j];
				d >>= 2;
			}
			dist[j][i] = dist[i][j];
		}
	}

	vector<int> brc_to_correct;
	for (int i = 0; i < num_barcodes; ++i)
	{
		int dmin = BARCODE_LENGTH + 1;
		for (int j = 0; j < num_barcodes; ++j)
			dmin = min(dmin, dist[i][j]);
		if (dmin >= D_MIN)
			brc_to_correct.push_back(i);
		//cout << i << ' ' << dmin << endl;
	}

	///to delete
	for (int i = 0; i < brc_to_correct.size(); ++i)
	{
		cout << brc_to_correct[i] << ' ' ;
	}


	cout << endl << "number of cell barcodes to error-correct: " << brc_to_correct.size() << endl;
	for (int i = 0; i < num_barcodes; i++)
		delete[] dist[i];
	delete[] dist;
	getchar();
	return 0;
}