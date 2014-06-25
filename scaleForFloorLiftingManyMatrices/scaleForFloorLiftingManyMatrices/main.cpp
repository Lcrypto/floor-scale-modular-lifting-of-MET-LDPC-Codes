
#include<iostream>
#include<string>
#include<algorithm>
#include<sstream>
#include<cctype>

#include".\myLib\emdOptimization.h"

using namespace std;
#define pii pair<int, int>
#define ll long long

const int DEFAULT_UPPER_DIST = 1000;
const int DEFAULT_UPPER_GIRTH = 10;
const int DEFAULT_TOP = 1;
//int girthFirst = 0;
//int aceFirst = 0;

int mingSumgMineSume = 0;//comparator: lexicographical order (min girth, sum girth, min emd, sum emd)

string toStr(ll x) {
    stringstream ss;
    ss << x;
    return ss.str();
}

bool checkInput(string MTR, string SIZES, int th7, int distUp, int upGirth, int mingSumgMineSume, int top) {
    bool validInput = 1;
    if (MTR == "") {
        validInput = 0;
        cerr << "wrong matrix file\n";
        cerr << "example: -matrices matrices.txt\n";
        cerr << "matrix format:\nn\nfilename_1\nfilename_2\n.\n.\n.\nfilename_n\n";
        cerr << endl;
    }
    if (SIZES == "") {
        validInput = 0;
        cerr << "wrong sizes\n";
        cerr << "example: -sizes sizes.txt\n";
        cerr << "sizes format:\nn\ncirc_1\tnumberOfAttemptsForOneCirc_1\ncirc_2\tnumberOfAttemptsForOneCirc_2\n.\n.\n.\n\ncirc_n\tnumberOfAttemptsForOneCirc_n";
        cerr << endl;
    }
    if (th7 == 0) {
        cerr << "you choose not to compute bound on upper distance\n";
        cerr << "you can turn on this feature by writing -th7 when you run this programm\n";
    }
    if ((th7 == 1) && (distUp == DEFAULT_UPPER_DIST)) {
        cerr << "you didn't give any initial upper bound on the distance of the code\n";
        cerr << "giving some bound may greatly increase the speed of this programm\n";
        cerr << "usually this bound is equal to the upper bound from protograph(theorem 8)\n";
        cerr << "example: -distUp 25\n";
    }
    if (upGirth == -1) {
        cerr << "you didn't give the value of upGirth\n";
        cerr << "this value means that EMD will be computed on cycles of length at most upGirth\n";
        cerr << "it is set to be equal to " << DEFAULT_UPPER_GIRTH << " by default\n";
        cerr << "example: -upGirth 6\n";
    }
    if (top == -1) {
        cerr << "you didn't give the value of top\n";
        cerr << "this value denotes the amount of best scale factors which would be printed\n";
        cerr << "0 means all\n";
        cerr << "it is set to be equal to " << DEFAULT_TOP << " by default\n";
        cerr << "example: -top 5\n";

    }
    if (mingSumgMineSume == 0) {
        cerr << "you didn't choose any comparator\n";
        cerr << "you can choose comparator 'mingSumgMineSume' by typing -mingSumgMineSume\n";
        cerr << "this comparator makes use of lexicographical order (min girth, sum girth, min emd, sum emd)\n";
        validInput =  0;

        //cerr << "now trivial partial order will be used, hence, for some circulants we will obtain several values\n";
    }
	//getchar();
    return validInput;
}

bool nextCombination(vector<int>& a, int n) {
    int k = (int)a.size();
    for (int i = k - 1; i >= 0; --i)
        if (a[i] < n - k + i + 1) {
            ++a[i];
            for (int j = i + 1; j < k; ++j)
                a[j] = a[j - 1] + 1;
            return true;
        }
    return false;
}

pii getGirthAndEmd(const vector<vector<vector<int> > >& mtr, int circ, int upGirth) {
    emdOpt opt(circ, upGirth, mtr);
    return opt.getGirthAndEmd();
}

//瑪雅混蛋
//for regular
vector<int> getPermanent(const vector<vector<int> >& a, vector<int>& used, int mod, int step = 0) {
    int n = a.size();
    vector<int> res(mod, 0);
    if (step + 1 == n) {
        for (int i = 0; i < n + 1; ++i) {
            if (used[i])
                continue;
            if (a[n - 1][i] == -1)
                return res;
            res[a[n - 1][i]] = 1;
            return res;
        }
    }
    for (int i = 0; i < n + 1; ++i) {
        if (used[i])
            continue;
        if (a[step][i] == -1)
            continue;
        used[i] = 1;
        vector<int> cur = getPermanent(a, used, mod, step + 1);
        for (int j = 0; j < cur.size(); ++j) {
            int x = j + a[step][i];
            if (x >= mod)
                x -= mod;
            res[x] ^= cur[j];
        }
        used[i] = 0;
    }
    return res;
}


//瑪雅混蛋
//for irregular
vector<int> getPermanent(const vector<vector<vector<int> > >& a, vector<int>& used, int mod, int step = 0) {
    int n = a.size();
    vector<int> res(mod, 0);
    if (step + 1 == n) {
        for (int i = 0; i < n + 1; ++i) {
            if (used[i])
                continue;
            for (int j = 0; j < a[n - 1][i].size(); ++j)
                res[a[n - 1][i][j]] = 1;
            return res;
        }
    }
    for (int i = 0; i < n + 1; ++i) {
        if (used[i])
            continue;
        if (a[step][i].empty())
            continue;
        used[i] = 1;
        vector<int> cur = getPermanent(a, used, mod, step + 1);
        for (int j = 0; j < cur.size(); ++j) {
            if (cur[j] == 0)
                continue;
            for (int jj = 0; jj < a[step][i].size(); ++jj) {
                int x = j + a[step][i][jj];
                if (x >= mod)
                    x -= mod;
                res[x] ^= cur[j];
            }
        }
        used[i] = 0;
    }
    return res;
}

//for regular
int getWeight(const vector<vector<int> >& a, int erInd, int mod) {
    int n = a.size();
    vector<int> used(n + 1, 0);
    used[erInd] = 1;
    vector<int> pol = getPermanent(a, used, mod);
    int res = 0;
    for (int i = 0; i < pol.size(); ++i)
        res += pol[i];
    return res;

}

//for irregular
int getWeight(const vector<vector<vector<int> > >& a, int erInd, int mod) {
    int n = a.size();
    vector<int> used(n + 1, 0);
    used[erInd] = 1;
    vector<int> pol = getPermanent(a, used, mod);
    int res = 0;
    for (int i = 0; i < pol.size(); ++i)
        res += pol[i];
    return res;
}

//for regular
int solve(const vector<int>& mask, const vector<vector<int> >& mtr, int mod) {
    vector<vector<int> > newMtr(mtr.size(), vector<int>(mask.size()));
    for (int i = 0; i < mtr.size(); ++i)
        for (int j = 0; j < mask.size(); ++j) {
            newMtr[i][j] = mtr[i][mask[j]];
        }
    int res = 0;
    for (int i = 0; i < mask.size(); ++i)
        res += getWeight(newMtr, i, mod);
    return res;
}

//for irregular
int solve(const vector<int>& mask, const vector<vector<vector<int> > >& mtr, int mod) {
    vector<vector<vector<int> > > newMtr(mtr.size(), vector<vector<int> >(mask.size()));
    for (int i = 0; i < mtr.size(); ++i)
        for (int j = 0; j < mask.size(); ++j) {
            newMtr[i][j] = mtr[i][mask[j]];
        }
    int res = 0;
    for (int i = 0; i < mask.size(); ++i)
        res += getWeight(newMtr, i, mod);
    return res;
}

//for regular
int countBound(const vector<vector<int> > & mtr, int mod) {
    int J = mtr.size(), I = mtr[0].size();
    if (I <= J)
        return -1;
    vector<int> mask(J + 1, 0);
    for (int i = 0; i < J + 1; ++i)
        mask[i] = i;
    int res = -1;
    do {
        int cur = solve(mask, mtr, mod);
        if (cur > 0) {
            if ((res < 0) || (cur < res))
                res = cur;
        }
    } while (nextCombination(mask, I - 1));
    return res;
}

//for irregular
int countBound(const vector<vector<vector<int> > > & mtr, int mod) {
    int J = mtr.size(), I = mtr[0].size();
    if (I <= J)
        return -1;
    vector<int> mask(J + 1, 0);
    for (int i = 0; i < J + 1; ++i)
        mask[i] = i;
    int res = -1;
    do {
        int cur = solve(mask, mtr, mod);
        if (cur > 0) {
            if ((res < 0) || (cur < res))
                res = cur;
        }
    } while (nextCombination(mask, I - 1));
    return res;
}

void print(const vector<int>& a) {
    for (int i = 0; i < a.size(); ++i)
        cout << a[i] << " ";
    cout << endl;
}


vector<int> parse(string s) {
    if ((s.empty()) || (s[0] == '-'))
        return vector<int>();
    vector<int> res;
    int x = 0;
    for (int i = 0; i < s.size(); ++i) {
        if (s[i] == '&') {
            res.push_back(x);
            x = 0;
        }
        else
            x = 10 * x + (s[i] - '0');
    }
    res.push_back(x);
    return res;
}

vector<vector<int> > getSmallProto(const vector<vector<int> >& proto, int var, int check) {
    vector<vector<int> > res(check, vector<int>(var));
    for (int i = 0; i < check; ++i)
        for (int j = 0; j < var; ++j)
            res[i][j] = proto[i][j];
    return res;
}




struct record {
    int scaleFactor;
    vector<int> girth, emd, dist;
    int minGirth;
    int sumGirth;
    int minEmd;
    int sumEmd;
    void compute() {
        minGirth = girth[0];
        minEmd = emd[0];
        sumEmd = 0;
        sumGirth = 0;
        for (int i = 0; i < girth.size(); ++i) {
            minGirth = min(minGirth, girth[i]);
            minEmd = min(minEmd, emd[i]);
            sumGirth += girth[i];
            sumEmd += emd[i];
        }
    }
    
    bool operator<=(const record& rec) const {
        if (mingSumgMineSume) {
            return (minGirth < rec.minGirth) ||
                ((minGirth == rec.minGirth) && (sumGirth < rec.sumGirth)) ||
                ((minGirth == rec.minGirth) && (sumGirth == rec.sumGirth) && (minEmd < rec.minEmd)) ||
                ((minGirth == rec.minGirth) && (sumGirth == rec.sumGirth) && (minEmd == rec.minEmd) && (sumEmd <= rec.sumEmd));
        }
        for (int i = 0; i < girth.size(); ++i) {
            if (girth[i] > rec.girth[i])
                return 0;
            if (emd[i] > rec.emd[i])
                return 0;
            if (dist[i] > rec.dist[i])
                return 0;
        }
        return 1;

        /*if (girthFirst) {
            return (girth < rec.girth) || ((girth == rec.girth) && (ace <= rec.ace));
        }
        if (aceFirst) {
            return (ace < rec.ace) || ((ace == rec.ace) && (girth <= rec.girth));
        }
        return (girth <= rec.girth) && (ace <= rec.ace) && (dist <= rec.dist);*/
    }
    bool operator<(const record& rec) const {
        if (mingSumgMineSume) {
            return (minGirth < rec.minGirth) ||
                ((minGirth == rec.minGirth) && (sumGirth < rec.sumGirth)) ||
                ((minGirth == rec.minGirth) && (sumGirth == rec.sumGirth) && (minEmd < rec.minEmd)) ||
                ((minGirth == rec.minGirth) && (sumGirth == rec.sumGirth) && (minEmd == rec.minEmd) && (sumEmd < rec.sumEmd));
        }
        for (int i = 0; i < girth.size(); ++i) {
            if (girth[i] > rec.girth[i])
                return 0;
            if (emd[i] > rec.emd[i])
                return 0;
            if (dist[i] >= rec.dist[i])
                return 0;
        }
        return 1;

        /*if (girthFirst) {
        return (girth < rec.girth) || ((girth == rec.girth) && (ace <= rec.ace));
        }
        if (aceFirst) {
        return (ace < rec.ace) || ((ace == rec.ace) && (girth <= rec.girth));
        }
        return (girth <= rec.girth) && (ace <= rec.ace) && (dist <= rec.dist);*/
    }
};


ostream& operator<<(ostream& os, const record& rec) {
    os << "scale factor = " << rec.scaleFactor << endl;
    for (int i = 0; i < rec.girth.size(); ++i) {
        os << "matrix " << i + 1 << ":\tgirth = " << rec.girth[i] << "\temd = " << rec.emd[i];
        if (rec.dist[i] != DEFAULT_UPPER_DIST) {
            os << "\tdist from th7 = " << rec.dist[i];
        }
        os << endl;
    }
    return os;
}

int main(int argc, char* argv[]) {
    //Initialization
    bool validInput = 1;
    vector<vector<int> > PROTOGRAPH;
    int CIRCULANT_SIZE = -1;
    ll VARIABLE_NODES;
    ll CHECK_NODES;
    string MTR_FILE = "";
    string SIZES_FILE = "";
    string COEF_FILE = "coef.txt";
    bool th7 = 0;
    int distUp = DEFAULT_UPPER_DIST;
    int upGirth = -1;
    int topX = -1;
    //reading parameters from cmd
    for (int i = 1; i < argc; ++i) {
        if (string(argv[i]) == "-matrices") {
            MTR_FILE = argv[i + 1];
            ++i;
            continue;
        }
        if (string(argv[i]) == "-sizes") {
            SIZES_FILE = argv[i + 1];
            ++i;
            continue;
        }
        if (string(argv[i]) == "-th7") {
            th7 = 1;
            continue;
        }
        if (string(argv[i]) == "-distUp") {
            string strDist = argv[i + 1];
            ++i;
            stringstream sstrDist(strDist);
            sstrDist >> distUp;
            continue;
        }
        if (string(argv[i]) == "-top") {
            string strTop = argv[i + 1];
            ++i;
            stringstream sstrTop(strTop);
            sstrTop >> topX;
            continue;
        }
        if (string(argv[i]) == "-upGirth") {
            string strGirth = argv[i + 1];
            ++i;
            stringstream sstrGirth(strGirth);
            sstrGirth >> upGirth;
            continue;
        }
        if (string(argv[i]) == "-mingSumgMineSume") {
            mingSumgMineSume = 1;
            continue;
        }
        if (string(argv[i]) == "-outFile") {
            COEF_FILE = argv[i + 1];
            ++i;
            continue;
        }
        
    }
    
    if ((!checkInput(MTR_FILE, SIZES_FILE, th7, distUp, upGirth, mingSumgMineSume, topX)) || (!validInput))
        return 0;
    if (upGirth == -1)
        upGirth = DEFAULT_UPPER_GIRTH;
    if (topX == -1)
        topX = DEFAULT_TOP;
    if (topX == 0)
        topX = 1000000000;
    

    //reading matrices -- START
    
    FILE* file = fopen(MTR_FILE.c_str(), "r");
    int numberOfMatrices;
    fscanf(file, "%d", &numberOfMatrices);
    vector<string> matrixFilenames(numberOfMatrices);
    for (int i = 0; i < numberOfMatrices; ++i) {
        string curFilename = "";
        char curChar = ' ';
        bool ok = 1;
        while (ok && (curFilename.empty() || (!isspace(curChar)))) {
            ok = EOF != fscanf(file, "%c", &curChar);
                
            if (ok && (!isspace(curChar)))
                curFilename.push_back(curChar);
        }
        matrixFilenames[i] = curFilename;
    }
    fclose(file);
    vector<int> varNodes(numberOfMatrices), checkNodes(numberOfMatrices), bigCircs(numberOfMatrices);
    vector<vector<vector<vector<int> > > > allMtrs(numberOfMatrices);
    vector<vector<vector<int> > > protographs(numberOfMatrices);
    for (int i = 0; i < numberOfMatrices; ++i) {
        file = fopen(matrixFilenames[i].c_str(), "r");
        fscanf(file, "%d%d%d", &varNodes[i], &checkNodes[i], &bigCircs[i]);
        allMtrs[i].assign(checkNodes[i], vector<vector<int> >(varNodes[i]));
        protographs[i].assign(checkNodes[i], vector<int>(varNodes[i]));

        CIRCULANT_SIZE = max(CIRCULANT_SIZE, bigCircs[i]);
        for (int r = 0; r < checkNodes[i]; ++r) {
            for (int c = 0; c < varNodes[i]; ++c) {
                string toParse = "";
                char curChar = ' ';
                bool ok = 1;
                while (ok && (toParse.empty() || (!isspace(curChar)))) {
                    ok = EOF != fscanf(file, "%c", &curChar);
                    if (ok && (!isspace(curChar)))
                        toParse.push_back(curChar);
                }
                allMtrs[i][r][c] = parse(toParse);
                protographs[i][r][c] = allMtrs[i][r][c].size();
            }
        }
        fclose(file);
    }

    //reading matrices -- END

    file = fopen(SIZES_FILE.c_str(), "r");
    int numberOfCircs;
    fscanf(file, "%d", &numberOfCircs);
    vector<int> circ(numberOfCircs), numOfIter(numberOfCircs);
    vector<vector<record> > records(numberOfCircs);
    for (int i = 0; i < numberOfCircs; ++i) {
        fscanf(file, "%d%d", &circ[i], &numOfIter[i]);
    }
    fclose(file);

    
    vector<vector<vector<vector<int> > > > newMtrs(numberOfMatrices);
    for (int i1 = 0; i1 < numberOfMatrices; ++i1) {
        newMtrs[i1].assign(checkNodes[i1], vector<vector<int> >(varNodes[i1]));
        for (int i2 = 0; i2 < checkNodes[i1]; ++i2) {
            for (int i3 = 0; i3 < varNodes[i1]; ++i3) {
                newMtrs[i1][i2][i3].resize(protographs[i1][i2][i3]);
            }
        }
    }

    for (int circId = 0; circId < numberOfCircs; ++circId) {
        cerr << "start to compute scale factor " << circId + 1 << "(circulant = " << circ[circId] << ")" << endl;
        for (int rIt = 1; rIt <= min(numOfIter[circId], CIRCULANT_SIZE); ++rIt) {
            //cerr << rIt << endl;
            int r = rIt;
            if (numOfIter[circId] < CIRCULANT_SIZE)
                r = rand() % CIRCULANT_SIZE;
            record cur;
            cur.scaleFactor = r;
            cur.dist.assign(numberOfMatrices, distUp);
            bool okScale = 1;
            for (int matrixId = 0; matrixId < numberOfMatrices; ++matrixId) {
                for (int i = 0; i < checkNodes[matrixId]; ++i) {
                    for (int j = 0; j < varNodes[matrixId]; ++j) {
                        for (int nodeId = 0; nodeId < newMtrs[matrixId][i][j].size(); ++nodeId) {
                            newMtrs[matrixId][i][j][nodeId] = (((allMtrs[matrixId][i][j][nodeId] * r) % bigCircs[matrixId]) * circ[circId]) / bigCircs[matrixId];
                        }

                        for (int i1 = 0; i1 < newMtrs[matrixId][i][j].size(); ++i1) {
                            for (int i2 = 0; i2 < i1; ++i2) {
                                if (newMtrs[matrixId][i][j][i1] == newMtrs[matrixId][i][j][i2]) {
                                    okScale = 0;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if (!okScale)
                continue;

            for (int matrixId = 0; matrixId < numberOfMatrices; ++matrixId) {
                pair<int, int> girthEmd = getGirthAndEmd(newMtrs[matrixId], circ[circId], upGirth);
                cur.girth.push_back(girthEmd.first);
                cur.emd.push_back(girthEmd.second);
            }
            cur.compute();
            /*bool goodRec = 1;
            for (int i = 0; i < records[circId].size(); ++i) {
                if (cur <= records[circId][i]) {
                    goodRec = 0;
                    break;
                }
            }
            if (!goodRec)
                continue;*/
            if (th7) {
                for (int matrixId = 0; matrixId < numberOfMatrices; ++matrixId) {
                    cur.dist[matrixId] = countBound(newMtrs[matrixId], circ[circId]);
                }
            }
            /*for(int i = 0; i < records[circId].size(); ++i) {
                if (cur <= records[circId][i]) {
                    goodRec = 0;
                    break;
                }
            }*/
            //if (goodRec) {
                records[circId].push_back(cur);
                //cerr << "new record for matrix " << circId + 1 << ":\t" << cur;
            //}
        }
        sort(records[circId].rbegin(), records[circId].rend());
        cerr << "best result for matrix " << circId + 1 << "\n";
        for (int i = 0; i < 1/*min(topX, (int)records[circId].size())*/; ++i) {
            cerr << i + 1 << ":\t" << records[circId][i];

        }
    }
    FILE* out = fopen("detailedOutput.txt", "w");
    for (int i = 0; i < records.size(); ++i) {
        fprintf(out, "circ = %d\n", circ[i]);
        cerr << "circ = " << circ[i] << endl;
        for (int j = 0; j < min(topX, (int)records[i].size()); ++j) {
            //cerr << records[i][j];
            if (th7)
                fprintf(out, "scale factor = %d\tmin girth = %d\tsum girth = %d\tmin emd on cycles of length <= %d = %d\tsum emd on cycles of length <= %d = %d\tdist from th7 = %d\n", 
                records[i][j].scaleFactor, records[i][j].minGirth, records[i][j].sumGirth, upGirth, records[i][j].minEmd, upGirth, records[i][j].sumEmd, records[i][j].dist);
            else
                fprintf(out, "scale factor = %d\tmin girth = %d\tsum girth = %d\tmin emd on cycles of length <= %d = %d\tsum emd on cycles of length <= %d = %d\n",
                records[i][j].scaleFactor, records[i][j].minGirth, records[i][j].sumGirth, upGirth, records[i][j].minEmd, upGirth, records[i][j].sumEmd);
        }
    }
    fclose(out);

    //if (!th7) {
        out = fopen(COEF_FILE.c_str(), "w");
        fprintf(out, "%d\n", records.size());
        for (int i = 0; i < records.size(); ++i) {
            if (records[i].empty()) {
                cerr << "there is no good scale factor for circulant " << circ[i] << "\n";
            }

            /*for (int j = 0; j < records[i].size(); ++j) {
                fprintf(out, "%d\t%d\n", circ[i], records[i][j].scaleFactor);

            }*/
            fprintf(out, "%d", circ[i]);
            for (int j = 0; j < min(topX, (int)records[i].size()); ++j) {
                fprintf(out, "\t%d", records[i][j].scaleFactor);
            }
            fprintf(out, "\n");
            //fprintf(out, "\n");

        }
        fclose(out);

    return 0;
}
