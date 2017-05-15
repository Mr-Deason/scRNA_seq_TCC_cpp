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

typedef  double MAT[MMAX + 2][MMAX + 2];

void LUBKSB(MAT A, int N, int np, int *INDX, double *B) {

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

	double AMAX, DUM, SUM, TINY;
	double VV[1000];
	int   I, IMAX, J, K;

	TINY = (double)1e-12;

	*D = 1; *CODE = 0;

	for (I = 1; I <= N; I++) {
		AMAX = 0.0;
		for (J = 1; J <= N; J++)
			if (fabs(A[I][J]) > AMAX) AMAX = (double)fabs(A[I][J]);
		if (AMAX < TINY) {
			*CODE = 1;
			return;
		}
		VV[I] = (double)1.0 / AMAX;
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
			DUM = VV[I] * (double)fabs(SUM);
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
		if ((double)fabs(A[J][J]) < TINY)  A[J][J] = TINY;

		if (J != N) {
			DUM = (double)1.0 / A[J][J];
			for (I = J + 1; I <= N; I++)  A[I][J] *= DUM;
		}
	} //j loop

} //LUDCMP()

int polyfit(const double* const dependentValues,
	const double* const independentValues,
	unsigned int        countOfElements,
	unsigned int        order,
	double*             coefficients)
{
	// Declarations...
	// ----------------------------------
	enum { maxOrder = 5 };

	double B[maxOrder + 1] = { 0.0f };
	double P[((maxOrder + 1) * 2) + 1] = { 0.0f };
	double A[(maxOrder + 1) * 2 * (maxOrder + 1)] = { 0.0f };

	double x, y, powx;

	unsigned int ii, jj, kk;

	// Verify initial conditions....
	// ----------------------------------

	// This method requires that the countOfElements > 
	// (order+1) 
	if (countOfElements <= order)
		return -1;

	// This method has imposed an arbitrary bound of
	// order <= maxOrder.  Increase maxOrder if necessary.
	if (order > maxOrder)
		return -1;

	// Begin Code...
	// ----------------------------------

	// Identify the column vector
	for (ii = 0; ii < countOfElements; ii++)
	{
		x = dependentValues[ii];
		y = independentValues[ii];
		powx = 1;

		for (jj = 0; jj < (order + 1); jj++)
		{
			B[jj] = B[jj] + (y * powx);
			powx = powx * x;
		}
	}

	// Initialize the PowX array
	P[0] = countOfElements;

	// Compute the sum of the Powers of X
	for (ii = 0; ii < countOfElements; ii++)
	{
		x = dependentValues[ii];
		powx = dependentValues[ii];

		for (jj = 1; jj < ((2 * (order + 1)) + 1); jj++)
		{
			P[jj] = P[jj] + powx;
			powx = powx * x;
		}
	}

	// Initialize the reduction matrix
	//
	for (ii = 0; ii < (order + 1); ii++)
	{
		for (jj = 0; jj < (order + 1); jj++)
		{
			A[(ii * (2 * (order + 1))) + jj] = P[ii + jj];
		}

		A[(ii*(2 * (order + 1))) + (ii + (order + 1))] = 1;
	}

	// Move the Identity matrix portion of the redux matrix
	// to the left side (find the inverse of the left side
	// of the redux matrix
	for (ii = 0; ii < (order + 1); ii++)
	{
		x = A[(ii * (2 * (order + 1))) + ii];
		if (x != 0)
		{
			for (kk = 0; kk < (2 * (order + 1)); kk++)
			{
				A[(ii * (2 * (order + 1))) + kk] =
					A[(ii * (2 * (order + 1))) + kk] / x;
			}

			for (jj = 0; jj < (order + 1); jj++)
			{
				if ((jj - ii) != 0)
				{
					y = A[(jj * (2 * (order + 1))) + ii];
					for (kk = 0; kk < (2 * (order + 1)); kk++)
					{
						A[(jj * (2 * (order + 1))) + kk] =
							A[(jj * (2 * (order + 1))) + kk] -
							y * A[(ii * (2 * (order + 1))) + kk];
					}
				}
			}
		}
		else
		{
			// Cannot work with singular matrices
			return -1;
		}
	}

	// Calculate and Identify the coefficients
	for (ii = 0; ii < (order + 1); ii++)
	{
		for (jj = 0; jj < (order + 1); jj++)
		{
			x = 0;
			for (kk = 0; kk < (order + 1); kk++)
			{
				x = x + (A[(ii * (2 * (order + 1))) + (kk + (order + 1))] *
					B[kk]);
			}
			coefficients[ii] = x;
		}
	}

	return 0;
}

void savgol_coeff(double *c, int np, int nl, int nr, int ld, int m) {
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
	double fac, sum;
	MAT   a;
	double b[MMAX + 2];

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
		for (k = 1; k <= nr; k++) sum += (double)pow(k, ipj);
		for (k = 1; k <= nl; k++) sum += (double)pow(-k, ipj);
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

void edge_fit(double *data, int window_start, int window_end, int interp_start, int interp_end, int polyorder, double *y)
{

	double *poly_coeff = (double*)malloc((polyorder + 1) * sizeof(double));
	memset(poly_coeff, 0, (polyorder + 1) * sizeof(double));

	int win_len = window_end - window_start;
	double *x = (double*)malloc(win_len * sizeof(double));
	memset(x, 0, win_len * sizeof(double));
	for (int i = 0; i < win_len; ++i)
		x[i] = i;
	polyfit(x, y + window_start, win_len, polyorder, poly_coeff);

	int interp_len = interp_end - interp_start;
	for (int i = 0; i < interp_len; ++i)
	{
		double tt = 1.0;
		data[i + interp_start] = 0.0;
		for (int j = 0; j <= polyorder; ++j)
		{
			data[i + interp_start] += tt*poly_coeff[j];
			tt *= x[i];
		}
	}

	free(poly_coeff);
	free(x);
}

double* savgol_filter(double *data, int n, int win_len, int polyorder)
{
	double* ret = (double*)malloc((n+2) * sizeof(double));
	memset(ret, 0, (n + 2) *sizeof(double));
	int nl = win_len / 2;
	int nr = win_len / 2;
	int m = polyorder;

	double *c = (double*)malloc((win_len + 2) * sizeof(double));
	memset(c, 0, (win_len + 2) * sizeof(double));
	savgol_coeff(c, nl + nr + 1, nl, nr, 0, m);

	//default mode - constant
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
	for (int i = 1; i <= n - nr; i++) {
		ret[i] = 0.0;
		for (j = 1; j <= nl + nr + 1; j++)
			if (i + index[j]>0)   //skip left points that do not exist.
				ret[i] += c[j] * data[i + index[j]-1];
	}
	free(index);
	
	//interp mode - using poly fit twice
	int half = win_len / 2;
	edge_fit(ret+1, 0, win_len, 0, half, m, data);
	edge_fit(ret+1, n - win_len, n, n - half, n, m, data);

	free(c);
	return ret+1;
}

void get_barcode()
{
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
	//all "read-I1_*" files
	for (int i = 0; i < files.size() / 2; ++i)
	{
		cout << files[i] << endl;
		gzFile gfp = gzopen(files[i].c_str(), "r");
		kseq_t *seq1;
		seq1 = kseq_init(gfp);
		int l;
		while ((l = kseq_read(seq1) >= 0))
		{
			string bar = seq1->seq.s;
			//printf("%s\n", bar.c_str());
			barcodes.push_back(encode(bar));
		}
		gzclose(gfp);
		kseq_destroy(seq1);
	}
	cout << barcodes.size() << endl;

	FILE* fp;

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
		cout << -cnt_bar[i].first << ' ' << decode(cnt_bar[i].second, BARCODE_LENGTH) << endl;

	double *diff = (double*)malloc(cnt_bar.size() * sizeof(double));
	for (int i = 0; i < cnt_bar.size() - 1; ++i)
	{
		diff[i] = cnt_bar[i].first - cnt_bar[i + 1].first;
	}
	int WINDOWS[2] = { 500, 5000 };
	double *yhat = savgol_filter(diff, cnt_bar.size() - 1, 151, 1);

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

	///to delete
	sort(codewords, codewords + num_barcodes);

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
		if (i < 10)
			cout << i << ' ' << dmin << endl;
	}

	fp = fopen("barcodes.dat", "wb");
	for (int i = 0; i < barcodes.size(); ++i)
		fprintf(fp, "%u\n", barcodes[i]);
	fclose(fp);
	fp = fopen("codewords.dat", "wb");
	for (int i = 0; i < num_barcodes; ++i)
		fprintf(fp, "%u\n", codewords[i]);
	fclose(fp);
	fp = fopen("brc_idx_to_correct.dat", "wb");
	for (int i = 0; i < brc_to_correct.size(); ++i)
		fprintf(fp, "%d\n", brc_to_correct[i]);
	fclose(fp);

	///to delete
	for (int i = 0; i < brc_to_correct.size(); ++i)
	{
		cout << brc_to_correct[i] << ' ';
	}


	cout << "Cell_barcodes_detected: " << num_barcodes << endl;
	cout << "NUM_OF_READS_in_CELL_BARCODES = " << num_reads << endl;
	cout << endl << "number of cell barcodes to error-correct: " << brc_to_correct.size() << endl;
	for (int i = 0; i < num_barcodes; i++)
		delete[] dist[i];
	delete[] dist;
}

void error_correct_and_split()
{
	static int BARCODE_LENGTH = 14;

	vector<unsigned int> barcodes;
	vector<unsigned int> codewords;
	vector<int> brc_idx_to_correct;

	unsigned int read;
	int idx;

	FILE *fp;
	fp = fopen("barcodes.dat", "rb");
	while (fscanf(fp, "%u", &read) != EOF)
		barcodes.push_back(read);
	fclose(fp);
	fp = fopen("codewords.dat", "rb");
	while (fscanf(fp, "%u", &read) != EOF)
		codewords.push_back(read);
	fclose(fp);
	fp = fopen("brc_idx_to_correct.dat", "rb");
	while (fscanf(fp, "%d", &idx) != EOF)
		brc_idx_to_correct.push_back(idx);
	fclose(fp);

	map<unsigned int, int> barcode_to_idx;
	for (int i = 0; i < codewords.size(); ++i)
		barcode_to_idx[codewords[i]] = i;

	set<unsigned int> brc_to_correct;
	for (int i = 0; i < brc_idx_to_correct.size(); ++i)
	{
		brc_to_correct.insert(codewords[brc_idx_to_correct[i]]);
	}

	///to do
	vector<vector<int> > ret;
	ret.resize(codewords.size());
	for (int i = 0; i < barcodes.size(); ++i)
	{
		unsigned int barcode = barcodes[i];
		if (barcode_to_idx.find(barcode) != barcode_to_idx.end())
		{
			ret[barcode_to_idx[barcode]].push_back(i);
		}
		else
		{
			bool flag = true;
			for (int j = 0; j < BARCODE_LENGTH && flag; ++j)
			{
				for (int k = 1; k < 4 && flag; ++k)
				{
					//unsigned int cousin = barcode ^ (k << (j * 2))
					unsigned int cousin = barcode ^ (k << (j << 1));
					if (brc_to_correct.find(cousin) != brc_to_correct.end())
					{
						ret[barcode_to_idx[cousin]].push_back(i);
						flag = false;
						break;
					}
				}
			}
		}
	}

	/*
	fp = fopen("ret.lst", "w");
	for (int i = 0; i < ret.size(); ++i)
	{
		for (int j = 0; j < ret[i].size(); ++j)
		{
			fprintf(fp, "%d ", ret[i][j]);
		}
		fprintf(fp, "\n");
	}
	fclose(fp);
	*/

	int NUM_OF_READS_in_CELL_BARCODES = 0;
	for (int i = 0; i < codewords.size(); ++i)
		NUM_OF_READS_in_CELL_BARCODES += ret[i].size();
	cout << "NUM_OF_READS_in_CELL_BARCODES (after error-correct): " << NUM_OF_READS_in_CELL_BARCODES << endl;


	vector<string> files;
	fs::path fastq_dir("../example_dataset/fastq_files/");
	if (exists(fastq_dir) && fs::is_directory(fastq_dir))
	{
		for (fs::directory_entry ite : fs::directory_iterator(fastq_dir))
			if (fs::is_regular_file(ite))
				files.push_back(ite.path().string());
		sort(files.begin(), files.end());
	}

	vector<int> line_byte_idx;
	line_byte_idx.push_back(0);
	int byte_cnt = 0;

	//all "read-RA_*" files
	cout << "merge all reads..." << endl;
	char *all_reads_file = "all_reads.fastq";
	fp = fopen(all_reads_file, "wb");
	char buff[256];
	int buff_len = 256;
	for (int i = files.size() / 2; i < files.size(); ++i)
	{
		gzFile gfp = gzopen(files[i].c_str(), "r");
		int len;
		while (len = gzread(gfp, buff, buff_len))
		{
			fwrite(buff, sizeof(char), len, fp);
			for (int j = 0; j < len; ++j)
			{
				if (buff[j] == '\n')
					line_byte_idx.push_back(byte_cnt + j + 1);
			}
			byte_cnt += len;
			if (len < buff_len)
				break;
		}
		gzclose(gfp);
	}
	fclose(fp);

	fp = fopen(all_reads_file, "r");
	int flag = 0;
	for (int i = 0; i < codewords.size(); ++i)
	{
		char filename[30], fastq_file[30], umi_file[30];
		sprintf(filename, "./out/cell_%04d_%s", i, decode(codewords[i], BARCODE_LENGTH).c_str());
		sprintf(fastq_file, "%s.fastq", filename);
		sprintf(umi_file, "%s.umi", filename);
		FILE *ffq = fopen(fastq_file, "wb");
		FILE *fum = fopen(umi_file, "wb");
		cout << "writing " << filename << endl;
		for (int j = 0; j < ret[i].size(); ++j)
		{
			unsigned int r = ret[i][j];
			int line = r * 8;
			fseek(fp, line_byte_idx[line] , SEEK_SET);
			for (;line < r*8 +6;++line)
			{ 
				int len = line_byte_idx[line + 1] - line_byte_idx[line];
				//fread(buff, sizeof(char), len, fp);
				fgets(buff, buff_len, fp);
				if (line < r * 8 + 4)
					//fwrite(buff, sizeof(char), len, ffq);
					fputs(buff, ffq);
				if (line > r * 8 + 4)
					//fwrite(buff, sizeof(char), len, fum);
					fputs(buff, fum);
			}
		}
		fclose(ffq);
		fclose(fum);
	}
	fclose(fp);

	getchar();
}

int main(int argc, char *argv[])
{
	//get_barcode();
	error_correct_and_split();
	return 0;
}